use vstd::prelude::*;
verus! {

use crate::pagetable::pagemap_util_t::*;
use crate::util::page_ptr_util_u::*;
use crate::pagetable::pagetable_spec::*;
use crate::pagetable::pagemap::*;
use crate::pagetable::entry::*;
use crate::define::*;
use vstd::simple_pptr::*;
use crate::lemma::lemma_u::*;

// exec
impl PageTable {
    // pub fn map_4k_page(&mut self, va:VAddr, dst: MapEntry)
    //     requires
    //         old(self).wf(),
    //         old(self).page_closure().contains(dst.addr) == false,
    //         old(self).mapping_4k()[va].is_None(),
    //         page_ptr_valid(dst.addr),
    // {
    // }
    pub fn get_entry_l4(&self, target_l4i: L4Index) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i < 512,
        ensures
            self.spec_resolve_mapping_l4(target_l4i) == ret,
            forall|l3i: L3Index, l2i: L2Index, l1i: L1Index|
                #![trigger spec_index2va((target_l4i, l3i, l2i, l1i))]
                #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, l3i, l2i, l1i)]
                0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i < 512 && ret.is_None()
                    ==> self.spec_resolve_mapping_4k_l1(target_l4i, l3i, l2i, l1i).is_None()
                    && self.mapping_4k().dom().contains(spec_index2va((target_l4i, l3i, l2i, l1i)))
                    == false,
    {
        let tracked l4_perm = self.l4_table.borrow().tracked_borrow(self.cr3);
        let l4_tbl: &PageMap = PPtr::<PageMap>::from_usize(self.cr3).borrow(Tracked(l4_perm));
        let l4_entry = l4_tbl.get(target_l4i);
        if l4_entry.perm.present {
            Some(l4_entry)
        } else {
            None
        }
    }

    pub fn get_entry_l3(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        l4_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            self.spec_resolve_mapping_l4(target_l4i) =~= Some(*l4_entry),
        ensures
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= ret,
            forall|l2i: L2Index, l1i: L1Index|
                #![trigger spec_index2va((target_l4i, target_l3i, l2i, l1i))]
                #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i)]
                0 <= l2i < 512 && 0 <= l1i < 512 && ret.is_None()
                    ==> self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, l2i, l1i).is_None()
                    && self.mapping_4k().dom().contains(
                    spec_index2va((target_l4i, target_l3i, l2i, l1i)),
                ) == false,
            ret.is_Some() ==> self.spec_resolve_mapping_1g_l3(target_l4i, target_l3i).is_None(),
    {
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l4_entry.addr);
        let l3_tbl: &PageMap = PPtr::<PageMap>::from_usize(l4_entry.addr).borrow(Tracked(l3_perm));
        let l3_entry = l3_tbl.get(target_l3i);
        if l3_entry.perm.present && !l3_entry.perm.ps {
            Some(l3_entry)
        } else {
            None
        }
    }

    pub fn get_entry_1g_l3(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        l4_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            self.spec_resolve_mapping_l4(target_l4i) =~= Some(*l4_entry),
        ensures
            self.spec_resolve_mapping_1g_l3(target_l4i, target_l3i) =~= ret,
    {
        let tracked l3_perm = self.l3_tables.borrow().tracked_borrow(l4_entry.addr);
        let l3_tbl: &PageMap = PPtr::<PageMap>::from_usize(l4_entry.addr).borrow(Tracked(l3_perm));
        let l3_entry = l3_tbl.get(target_l3i);
        if l3_entry.perm.present && l3_entry.perm.ps {
            Some(l3_entry)
        } else {
            None
        }
    }

    pub fn get_entry_l2(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        l3_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= Some(*l3_entry),
        ensures
            self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) =~= ret,
            forall|l1i: L1Index|
                #![trigger spec_index2va((target_l4i, target_l3i, target_l2i, l1i))]
                #![trigger self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, l1i)]
                0 <= l1i < 512 && ret.is_None() ==> self.spec_resolve_mapping_4k_l1(
                    target_l4i,
                    target_l3i,
                    target_l2i,
                    l1i,
                ).is_None() && self.mapping_4k().dom().contains(
                    spec_index2va((target_l4i, target_l3i, target_l2i, l1i)),
                ) == false,
    {
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l3_entry.addr);
        let l2_tbl: &PageMap = PPtr::<PageMap>::from_usize(l3_entry.addr).borrow(Tracked(l2_perm));
        let l2_entry = l2_tbl.get(target_l2i);
        if l2_entry.perm.present && !l2_entry.perm.ps {
            Some(l2_entry)
        } else {
            None
        }
    }

    pub fn get_entry_2m_l2(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        l3_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            self.spec_resolve_mapping_l3(target_l4i, target_l3i) =~= Some(*l3_entry),
        ensures
            self.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i) =~= ret,
    {
        let tracked l2_perm = self.l2_tables.borrow().tracked_borrow(l3_entry.addr);
        let l2_tbl: &PageMap = PPtr::<PageMap>::from_usize(l3_entry.addr).borrow(Tracked(l2_perm));
        let l2_entry = l2_tbl.get(target_l2i);
        if l2_entry.perm.present && l2_entry.perm.ps {
            Some(l2_entry)
        } else {
            None
        }
    }

    pub fn get_entry_l1(
        &self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        l2_entry: &PageEntry,
    ) -> (ret: Option<PageEntry>)
        requires
            self.wf(),
            self.kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
            self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i) =~= Some(*l2_entry),
        ensures
            self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i) =~= ret,
            self.mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) =~= ret.is_Some(),
            ret.is_Some() ==> self.mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) && self.mapping_4k()[spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i))]
                == page_entry_to_map_entry(&ret.unwrap()),
    {
        let tracked l1_perm = self.l1_tables.borrow().tracked_borrow(l2_entry.addr);
        let l1_tbl: &PageMap = PPtr::<PageMap>::from_usize(l2_entry.addr).borrow(Tracked(l1_perm));
        let l1_entry = l1_tbl.get(target_l1i);
        let ret = if l1_entry.perm.present {
            Some(l1_entry)
        } else {
            None
        };
        ret
    }

    pub fn create_entry_l4(
        &mut self,
        target_l4i: L4Index,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            old(self).spec_resolve_mapping_l4(target_l4i).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            old(self).page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            self.wf(),
            self.kernel_l4_end == old(self).kernel_l4_end,
            self.pcid == old(self).pcid,
            self.page_closure() =~= old(self).page_closure().insert(page_map_ptr),
            self.mapping_4k() =~= old(self).mapping_4k(),
            self.mapping_2m() =~= old(self).mapping_2m(),
            self.mapping_1g() =~= old(self).mapping_1g(),
            self.spec_resolve_mapping_l4(target_l4i).is_Some(),
            self.spec_resolve_mapping_l4(target_l4i).get_Some_0().addr == page_map_ptr,
            self.kernel_entries =~= old(self).kernel_entries,
    {
        let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
        page_map_set(
            self.cr3,
            Tracked(&mut l4_perm),
            target_l4i,
            PageEntry {
                addr: page_map_ptr,
                perm: PageEntryPerm {
                    present: true,
                    ps: false,
                    write: true,
                    execute_disable: false,
                    user: true,
                },
            },
        );
    }

    pub fn create_entry_l3(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l3_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            old(self).spec_resolve_mapping_l4(target_l4i).is_Some(),
            old(self).spec_resolve_mapping_l4(target_l4i).get_Some_0().addr == target_l3_p,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i).is_None(),
            old(self).spec_resolve_mapping_1g_l3(target_l4i, target_l3i).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            old(self).page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            self.wf(),
            self.kernel_l4_end == old(self).kernel_l4_end,
            self.page_closure() =~= old(self).page_closure().insert(page_map_ptr),
            self.mapping_4k() =~= old(self).mapping_4k(),
            self.mapping_2m() =~= old(self).mapping_2m(),
            self.mapping_1g() =~= old(self).mapping_1g(),
            self.spec_resolve_mapping_l4(target_l4i) == old(self).spec_resolve_mapping_l4(
                target_l4i,
            ),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i).is_Some(),
            self.spec_resolve_mapping_l3(target_l4i, target_l3i).get_Some_0().addr == page_map_ptr,
            self.spec_resolve_mapping_1g_l3(target_l4i, target_l3i).is_None(),
            self.kernel_entries =~= old(self).kernel_entries,
    {
        let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        
        page_map_set(
            target_l3_p,
            Tracked(&mut l3_perm),
            target_l3i,
            PageEntry {
                addr: page_map_ptr,
                perm: PageEntryPerm {
                    present: true,
                    ps: false,
                    write: true,
                    execute_disable: false,
                    user: true,
                },
            },
        );
    }

    pub fn create_entry_l2(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        page_map_ptr: PageMapPtr,
        Tracked(page_map_perm): Tracked<PointsTo<PageMap>>,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i).is_Some(),
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i).get_Some_0().addr
                == target_l2_p,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).is_None(),
            old(self).spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i).is_None(),
            page_ptr_valid(page_map_ptr),
            old(self).page_closure().contains(page_map_ptr) == false,
            old(self).page_not_mapped(page_map_ptr),
            page_map_perm.addr() == page_map_ptr,
            page_map_perm.is_init(),
            page_map_perm.value().wf(),
            forall|i: usize|
                #![trigger page_map_perm.value()[i].is_empty()]
                0 <= i < 512 ==> page_map_perm.value()[i].is_empty(),
        ensures
            self.wf(),
            self.kernel_l4_end == old(self).kernel_l4_end,
            self.page_closure() =~= old(self).page_closure().insert(page_map_ptr),
            self.mapping_4k() =~= old(self).mapping_4k(),
            self.mapping_2m() =~= old(self).mapping_2m(),
            self.mapping_1g() =~= old(self).mapping_1g(),
            self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).is_Some(),
            self.spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).get_Some_0().addr
                == page_map_ptr,
            self.spec_resolve_mapping_2m_l2(target_l4i, target_l3i, target_l2i).is_None(),
            self.kernel_entries =~= old(self).kernel_entries,
    {
        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);

        page_map_set(
            target_l2_p,
            Tracked(&mut l2_perm),
            target_l2i,
            PageEntry {
                addr: page_map_ptr,
                perm: PageEntryPerm {
                    present: true,
                    ps: false,
                    write: true,
                    execute_disable: false,
                    user: true,
                },
            },
        );
    }

    pub fn map_4k_page(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
        target_entry: &MapEntry,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).is_Some(),
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).get_Some_0().addr
                == target_l1_p,
            old(self).spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ).is_None() || old(self).mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) == false,
            old(self).page_closure().contains(target_entry.addr) == false,
            page_ptr_valid(target_entry.addr),
        ensures
            self.wf(),
            self.kernel_l4_end == old(self).kernel_l4_end,
            self.page_closure() =~= old(self).page_closure(),
            self.mapping_4k@ == old(self).mapping_4k@.insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
                *target_entry,
            ),
            self.mapping_2m() =~= old(self).mapping_2m(),
            self.mapping_1g() =~= old(self).mapping_1g(),
            self.kernel_entries =~= old(self).kernel_entries,
    {

        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(target_l1_p);
        page_map_set(
            target_l1_p,
            Tracked(&mut l1_perm),
            target_l1i,
            PageEntry {
                addr: target_entry.addr,
                perm: PageEntryPerm {
                    present: true,
                    ps: false,
                    write: target_entry.write,
                    execute_disable: target_entry.execute_disable,
                    user: true,
                },
            },
        );
    }

    /// Precondition:
    /// This unmap method will only be called when all previous level exists, and target entry exists in pagetable
    /// The VA -> PA mapping should exist.
    ///
    /// Postcondition:
    /// unmap will need to delete target entry mappings in mapping_4k (VA->PA),
    /// PageMaps lx_tables should not change.
    pub fn unmap_4k_page(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l1i: L2Index,
        target_l1_p: PageMapPtr,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            0 <= target_l1i < 512,
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).is_Some(),
            old(self).spec_resolve_mapping_l2(target_l4i, target_l3i, target_l2i).get_Some_0().addr
                == target_l1_p,
            old(self).spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                target_l1i,
            ).is_Some() || old(self).mapping_4k().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ) == true,
        ensures
            self.wf(),
            self.kernel_l4_end == old(self).kernel_l4_end,
            self.page_closure() =~= old(self).page_closure(),
            self.mapping_4k@ == old(self).mapping_4k@.remove(
                spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)),
            ),
            self.spec_resolve_mapping_4k_l1(target_l4i, target_l3i, target_l2i, target_l1i).is_None(),
            self.mapping_2m() =~= old(self).mapping_2m(),
            self.mapping_1g() =~= old(self).mapping_1g(),
            self.kernel_entries =~= old(self).kernel_entries,
    {
        broadcast use PageTable::reveal_page_table_wf;
        broadcast use PageTable::reveal_page_table_levels_wf;
        // broadcast use PageTable::reveal_page_table_disjoint_wf;
        // broadcast use PageTable::reveal_page_table_mappings_wf;
        // broadcast use PageTable::reveal_page_table_addtional_wf;

        let va = Ghost(spec_index2va((target_l4i, target_l3i, target_l2i, target_l1i)));
        assert(va_4k_valid(va@)) by {
            va_lemma();
        };
        assert(self.mapping_4k@.dom().contains(va@)) by { broadcast use PageTable::reveal_page_table_mappings_wf; };
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(target_l1_p);
        page_map_set(target_l1_p, Tracked(&mut l1_perm), target_l1i, PageEntry::empty());

        proof {
            self.l1_tables.borrow_mut().tracked_insert(target_l1_p, l1_perm);
            self.mapping_4k@ = self.mapping_4k@.remove(va@);
            assert(!self.mapping_4k@.contains_key(va@));
        }

        // we need to flush the tlb for all cores.
        assert(self.tlb_mapping_4k@.len() == NUM_CPUS) by { broadcast use PageTable::reveal_page_table_addtional_wf; };
        self.tlb_mapping_4k = flush_tlb_4kentry(self.tlb_mapping_4k, va);

        assert(self.tlb_submap_of_mapping()) by {
            broadcast use PageTable::reveal_page_table_addtional_wf;
            assert(old(self).mapping_4k@.remove(va@) =~= self.mapping_4k@);
            assert(forall|cpu_id: CpuId|
                #![auto]
                0 <= cpu_id < NUM_CPUS ==> self.tlb_mapping_4k@[cpu_id as int].submap_of(
                    old(self).tlb_mapping_4k@[cpu_id as int],
                )  // from flush_tlb_4kentry
                 && old(self).tlb_mapping_4k@[cpu_id as int].submap_of(
                    old(self).mapping_4k@,
                )  // from precondition
            );
            broadcast use submap_by_transitivity;  // show transitivity, so below can be proved.

            assert(forall|cpu_id: CpuId|
                #![auto]
                0 <= cpu_id < NUM_CPUS ==> self.tlb_mapping_4k@[cpu_id as int].submap_of(
                    old(self).mapping_4k@,
                ));
        };

        assert(self.wf_l4());
        assert(self.wf_l3());
        assert(self.wf_l2());
        assert(self.wf_l1());
        assert(self.disjoint_l4()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
        assert(self.disjoint_l3()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
        assert(self.disjoint_l2()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
        assert(self.disjoint_wf()) by { broadcast use PageTable::reveal_page_table_disjoint_wf; };
        assert(self.wf_mapping_4k()) by {
            broadcast use PageTable::reveal_page_table_mappings_wf;
            va_lemma();
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                #![trigger self.mapping_4k@.dom().contains(spec_index2va((l4i,l3i,l2i,l1i)))]
                #![trigger old(self).mapping_4k@.dom().contains(spec_index2va((l4i,l3i,l2i,l1i)))]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i
                    < 512 && !((target_l4i, target_l3i, target_l2i, target_l1i) =~= (
                    l4i,
                    l3i,
                    l2i,
                    l1i,
                )) ==> self.mapping_4k@.dom().contains(spec_index2va((l4i, l3i, l2i, l1i))) == old(
                    self,
                ).mapping_4k@.dom().contains(spec_index2va((l4i, l3i, l2i, l1i))));

            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && !((
                    target_l4i,
                    target_l3i,
                    target_l2i,
                ) =~= (l4i, l3i, l2i)) ==> self.spec_resolve_mapping_l2(l4i, l3i, l2i) =~= old(
                    self,
                ).spec_resolve_mapping_l2(l4i, l3i, l2i));

            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger self.spec_resolve_mapping_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512
                    && self.spec_resolve_mapping_l2(l4i, l3i, l2i).is_Some() && !((
                    target_l4i,
                    target_l3i,
                    target_l2i,
                ) =~= (l4i, l3i, l2i)) ==> self.spec_resolve_mapping_l2(
                    l4i,
                    l3i,
                    l2i,
                ).get_Some_0().addr != target_l1_p) by {
                old(self).internal_resolve_disjoint();
            };

            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                #![trigger old(self).spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i
                    < 512 && !((target_l4i, target_l3i, target_l2i) =~= (l4i, l3i, l2i))
                    ==> self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).is_Some() == old(
                    self,
                ).spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).is_Some());

            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index, l1i: L2Index|
                #![trigger self.mapping_4k@[spec_index2va((l4i,l3i,l2i,l1i))]]
                #![trigger self.spec_resolve_mapping_4k_l1(l4i,l3i,l2i,l1i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 && 0 <= l1i
                    < 512 ==> self.mapping_4k@.dom().contains(spec_index2va((l4i, l3i, l2i, l1i)))
                    == self.spec_resolve_mapping_4k_l1(l4i, l3i, l2i, l1i).is_Some());
        };
        assert(self.wf_mapping_2m()) by {
            broadcast use PageTable::reveal_page_table_mappings_wf;
            assert(forall|l4i: L4Index, l3i: L3Index, l2i: L2Index|
                #![trigger self.spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                #![trigger old(self).spec_resolve_mapping_2m_l2(l4i,l3i,l2i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && 0 <= l2i < 512 ==> old(
                    self,
                ).spec_resolve_mapping_2m_l2(l4i, l3i, l2i) == self.spec_resolve_mapping_2m_l2(
                    l4i,
                    l3i,
                    l2i,
                ));
        };
        assert(self.wf_mapping_1g()) by {
            broadcast use PageTable::reveal_page_table_mappings_wf;
            assert(forall|l4i: L4Index, l3i: L3Index|
                #![trigger self.spec_resolve_mapping_1g_l3(l4i,l3i)]
                #![trigger old(self).spec_resolve_mapping_1g_l3(l4i,l3i)]
                self.kernel_l4_end <= l4i < 512 && 0 <= l3i < 512 && (l4i, l3i) != (
                    target_l4i,
                    target_l3i,
                ) ==> old(self).spec_resolve_mapping_1g_l3(l4i, l3i)
                    =~= self.spec_resolve_mapping_1g_l3(l4i, l3i));
        };
        assert(self.mappings_wf()) by { broadcast use PageTable::reveal_page_table_mappings_wf; };
        // assert(self.user_only());
        // assert(self.rwx_upper_level_entries());
        // assert(self.present_or_zero());
        // assert(self.table_pages_wf());
        assert(self.additonal_wf()) by {broadcast use PageTable::reveal_page_table_addtional_wf;}
        assert(self.mapping_2m() =~= old(self).mapping_2m());
        assert(self.mapping_1g() =~= old(self).mapping_1g());
    }

    pub fn map_2m_page(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        target_entry: &MapEntry,
    )
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i).is_Some(),
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i).get_Some_0().addr
                == target_l2_p,
            old(self).spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_None(),
            old(self).spec_resolve_mapping_2m_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_None() || old(self).mapping_2m().dom().contains(
                spec_index2va((target_l4i, target_l3i, target_l2i, 0)),
            ) == false,
            old(self).page_closure().contains(target_entry.addr) == false,
            page_ptr_valid(target_entry.addr),
            page_ptr_2m_valid(target_entry.addr),
        ensures
            self.wf(),
            self.kernel_l4_end == old(self).kernel_l4_end,
            self.page_closure() =~= old(self).page_closure(),
            self.mapping_2m@ == old(self).mapping_2m@.insert(
                spec_index2va((target_l4i, target_l3i, target_l2i, 0)),
                *target_entry,
            ),
            self.mapping_4k() =~= old(self).mapping_4k(),
            self.mapping_1g() =~= old(self).mapping_1g(),
            self.kernel_entries =~= old(self).kernel_entries,
    {
        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        page_map_set(
            target_l2_p,
            Tracked(&mut l2_perm),
            target_l2i,
            PageEntry {
                addr: target_entry.addr,
                perm: PageEntryPerm {
                    present: true,
                    ps: true,
                    write: target_entry.write,
                    execute_disable: target_entry.execute_disable,
                    user: true,
                },
            },
        );
    }

    pub fn remove_l2_entry(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l2i: L2Index,
        target_l2_p: PageMapPtr,
        target_l1_p: PageMapPtr,
    ) -> (ret:(PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            0 <= target_l2i < 512,
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i).is_Some(),
            old(self).spec_resolve_mapping_l3(target_l4i, target_l3i).get_Some_0().addr
                == target_l2_p,
            old(self).spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).is_Some(),
            old(self).spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                target_l2i,
            ).unwrap().addr == target_l1_p,
            forall|i: L1Index| #![auto] 0 <= i < 512 ==> old(self).spec_resolve_mapping_4k_l1(
                target_l4i,
                target_l3i,
                target_l2i,
                i
            ).is_None(),
        ensures
            self.wf(),
            self.kernel_l4_end == old(self).kernel_l4_end,
            self.page_closure() =~= old(self).page_closure().remove(target_l1_p),
            self.mapping_2m() == old(self).mapping_2m(),
            self.mapping_4k() =~= old(self).mapping_4k(),
            self.mapping_1g() =~= old(self).mapping_1g(),
            self.kernel_entries =~= old(self).kernel_entries,
            ret.0 == target_l1_p,
            ret.1@.is_init(),
            ret.1@.addr() == target_l1_p,
    {
        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        page_map_set(
            target_l2_p,
            Tracked(&mut l2_perm),
            target_l2i,
            PageEntry {
                addr: 0,
                perm: PageEntryPerm {
                    present: false,
                    ps: false,
                    write: false,
                    execute_disable: false,
                    user: false,
                },
            },
        );
        let tracked mut l1_perm = self.l1_tables.borrow_mut().tracked_remove(target_l1_p);
        let ret = (target_l1_p, Tracked(l1_perm));
        return ret;
    }

    pub fn remove_l3_entry(
        &mut self,
        target_l4i: L4Index,
        target_l3i: L3Index,
        target_l3_p: PageMapPtr,
        target_l2_p: PageMapPtr,
    ) -> (ret:(PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            0 <= target_l3i < 512,
            old(self).spec_resolve_mapping_l4(target_l4i).is_Some(),
            old(self).spec_resolve_mapping_l4(target_l4i).get_Some_0().addr
                == target_l3_p,
            old(self).spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).is_Some(),old(self).spec_resolve_mapping_1g_l3(
                target_l4i,
                target_l3i,
            ).is_None(),
            old(self).spec_resolve_mapping_l3(
                target_l4i,
                target_l3i,
            ).unwrap().addr == target_l2_p,
            forall|i: L2Index| #![auto] 0 <= i < 512 ==> old(self).spec_resolve_mapping_l2(
                target_l4i,
                target_l3i,
                i
            ).is_None(),
            forall|i: L2Index| #![auto] 0 <= i < 512 ==> old(self).spec_resolve_mapping_2m_l2(
                target_l4i,
                target_l3i,
                i
            ).is_None(),
        ensures
            self.wf(),
            self.kernel_l4_end == old(self).kernel_l4_end,
            self.page_closure() =~= old(self).page_closure().remove(target_l2_p),
            self.mapping_2m() == old(self).mapping_2m(),
            self.mapping_4k() =~= old(self).mapping_4k(),
            self.mapping_1g() =~= old(self).mapping_1g(),
            self.kernel_entries =~= old(self).kernel_entries,
            ret.0 == target_l2_p,
            ret.1@.is_init(),
            ret.1@.addr() == target_l2_p,
    {
    
        let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        page_map_set(
            target_l3_p,
            Tracked(&mut l3_perm),
            target_l3i,
            PageEntry {
                addr: 0,
                perm: PageEntryPerm {
                    present: false,
                    ps: false,
                    write: false,
                    execute_disable: false,
                    user: false,
                },
            },
        );

        let tracked mut l2_perm = self.l2_tables.borrow_mut().tracked_remove(target_l2_p);
        let ret = (target_l2_p, Tracked(l2_perm));
        return ret;
    }

    pub fn remove_l4_entry(
        &mut self,
        target_l4i: L4Index,
        target_l3_p: PageMapPtr,
    ) -> (ret:(PageMapPtr, Tracked<PointsTo<PageMap>>))
        requires
            old(self).wf(),
            old(self).kernel_l4_end <= target_l4i < 512,
            old(self).spec_resolve_mapping_l4(target_l4i).is_Some(),
            old(self).spec_resolve_mapping_l4(target_l4i).get_Some_0().addr
                == target_l3_p,
            forall|i: L3Index| #![auto] 0 <= i < 512 ==> old(self).spec_resolve_mapping_l3(
                target_l4i,
                i
            ).is_None(),
            forall|i: L3Index| #![auto] 0 <= i < 512 ==> old(self).spec_resolve_mapping_1g_l3(
                target_l4i,
                i
            ).is_None(),
        ensures
            // self.wf(),
            // self.kernel_l4_end == old(self).kernel_l4_end,
            // self.page_closure() =~= old(self).page_closure().remove(target_l3_p),
            // self.mapping_2m() == old(self).mapping_2m(),
            // self.mapping_4k() =~= old(self).mapping_4k(),
            // self.mapping_1g() =~= old(self).mapping_1g(),
            // self.kernel_entries =~= old(self).kernel_entries,
            // ret.0 == target_l3_p,
            // ret.1@.is_init(),
            // ret.1@.addr() == target_l3_p,
    {

        let tracked mut l4_perm = self.l4_table.borrow_mut().tracked_remove(self.cr3);
        page_map_set(
            self.cr3,
            Tracked(&mut l4_perm),
            target_l4i,
            PageEntry {
                addr: 0,
                perm: PageEntryPerm {
                    present: false,
                    ps: false,
                    write: false,
                    execute_disable: false,
                    user: false,
                },
            },
        );
        let tracked mut l3_perm = self.l3_tables.borrow_mut().tracked_remove(target_l3_p);
        let ret = (target_l3_p, Tracked(l3_perm));
        return ret;
    }

}

} // verus!
