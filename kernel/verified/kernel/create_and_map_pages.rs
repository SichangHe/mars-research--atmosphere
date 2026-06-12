use vstd::prelude::*;
verus! {

// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_proof::*;
// use crate::util::page_ptr_util_u::*;
use crate::lemma::lemma_t::*;
use crate::lemma::lemma_u::*;
use crate::util::page_ptr_util_u::*;
use crate::define::*;

// use crate::trap::*;
// use crate::pagetable::pagemap_util_t::*;
use crate::pagetable::entry::*;
use crate::kernel::Kernel;
use crate::va_range::VaRange4K;

impl Kernel {
    pub open spec fn address_space_range_free(
        &self,
        target_proc_ptr: ProcPtr,
        va_range: &VaRange4K,
    ) -> bool {
        forall|j: int|
            #![auto]
            0 <= j < va_range.len ==> self.get_address_space(target_proc_ptr).dom().contains(
                va_range@[j],
            ) == false
    }

    pub open spec fn io_space_range_free(
        &self,
        target_proc_ptr: ProcPtr,
        va_range: &VaRange4K,
    ) -> bool {
        forall|j: int|
            #![auto]
            0 <= j < va_range.len ==> self.get_io_space(target_proc_ptr).dom().contains(
                va_range@[j],
            ) == false
    }

    pub fn check_address_space_va_range_free(
        &self,
        target_proc_ptr: ProcPtr,
        va_range: &VaRange4K,
    ) -> (ret: bool)
        requires
            self.wf(),
            self.proc_dom().contains(target_proc_ptr),
            va_range.wf(),
        ensures
            ret == self.address_space_range_free(target_proc_ptr, va_range),
    {
        let target_pcid = self.proc_man.get_proc(target_proc_ptr).pcid;
        for i in 0..va_range.len
        {
            if self.mem_man.resolve_pagetable_mapping(target_pcid, va_range.index(i)).is_some() {
                return false;
            }
        }
        return true;
    }

    pub fn check_io_space_va_range_free(
        &self,
        target_proc_ptr: ProcPtr,
        va_range: &VaRange4K,
    ) -> (ret: bool)
        requires
            self.wf(),
            self.proc_dom().contains(target_proc_ptr),
            self.get_proc(target_proc_ptr).ioid.is_Some(),
            va_range.wf(),
        ensures
            ret == self.io_space_range_free(target_proc_ptr, va_range),
    {
        let target_ioid = self.proc_man.get_proc(target_proc_ptr).ioid.unwrap();
        for i in 0..va_range.len
        {
            if self.mem_man.resolve_iommu_table_mapping(target_ioid, va_range.index(i)).is_some() {
                return false;
            }
        }
        return true;
    }

    pub fn alloc_and_map(
        &mut self,
        target_proc_ptr: ProcPtr,
        target_va: VAddr,
        tagret_l1_p: PageMapPtr,
    ) -> (ret: MapEntry)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(target_proc_ptr),
            old(self).get_container_quota(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).mem_4k >= 1,
            old(self).get_num_of_free_pages() >= 1,
            va_4k_valid(target_va),
            old(self).get_address_space(target_proc_ptr).dom().contains(target_va) == false,
            old(self).mem_man.get_pagetable_by_pcid(
                old(self).get_proc(target_proc_ptr).pcid,
            ).unwrap().spec_resolve_mapping_l2(
                spec_va2index(target_va).0,
                spec_va2index(target_va).1,
                spec_va2index(target_va).2,
            ).is_Some(),
            old(self).mem_man.get_pagetable_by_pcid(
                old(self).get_proc(target_proc_ptr).pcid,
            ).unwrap().spec_resolve_mapping_l2(
                spec_va2index(target_va).0,
                spec_va2index(target_va).1,
                spec_va2index(target_va).2,
            ).unwrap().addr == tagret_l1_p,
        ensures
            self.wf(),
            self.proc_dom() == old(self).proc_dom(),
            self.thread_dom() == old(self).thread_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - 1,
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && p_ptr != target_proc_ptr
                    ==> self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr),
            forall|t_ptr: ThreadPtr|
                #![auto]
                self.thread_dom().contains(t_ptr) ==> self.get_thread(t_ptr) =~= old(
                    self,
                ).get_thread(t_ptr),
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(
                    target_proc_ptr,
                ).owning_container ==> self.get_container(c_ptr) =~= old(self).get_container(c_ptr)
                    && self.get_container_owned_pages(c_ptr) =~= old(
                    self,
                ).get_container_owned_pages(c_ptr),
            forall|e_ptr: EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
                    self,
                ).get_endpoint(e_ptr),
            forall|p: Pcid|
                #![trigger self.mem_man.pcid_active(p)]
                #![trigger self.mem_man.pcid_to_proc_ptr(p)]
                self.mem_man.pcid_active(p) ==> old(self).mem_man.pcid_to_proc_ptr(p)
                    == self.mem_man.pcid_to_proc_ptr(p),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_procs,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).parent_rev_ptr,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).children,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_endpoints,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_threads,
            // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
            // self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_cpus,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).scheduler,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).subtree_set
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).subtree_set,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).depth =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).depth,
            old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).quota.spec_subtract_mem_4k(
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).quota,
                1,
            ),
            self.get_address_space(target_proc_ptr) =~= old(self).get_address_space(
                target_proc_ptr,
            ).insert(target_va, ret),
            old(self).page_alloc.page_is_mapped(ret.addr) == false,
            self.page_alloc.page_is_mapped(ret.addr),
            forall|p: PagePtr|
                #![trigger self.page_alloc.page_is_mapped(p)]
                p != ret.addr ==> self.page_alloc.page_is_mapped(p) == old(
                    self,
                ).page_alloc.page_is_mapped(p),
            self.page_mapping@.dom() == old(self).page_mapping@.dom().insert(ret.addr),
            forall|page_ptr: PagePtr|
                #![trigger self.page_mapping@[page_ptr]]
                old(self).page_mapping@.dom().contains(page_ptr) ==> old(
                    self,
                ).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
            self.page_mapping@[ret.addr] == Set::empty().insert((target_proc_ptr, target_va)),
    {
        let target_container_ptr = self.proc_man.get_proc(target_proc_ptr).owning_container;
        let old_quota = self.proc_man.get_container(target_container_ptr).quota.mem_4k;
        let target_pcid = self.proc_man.get_proc(target_proc_ptr).pcid;
        let (l4i, l3i, l2i, l1i) = va2index(target_va);
        let new_page_ptr = self.page_alloc.alloc_and_map_4k(
            target_pcid,
            target_va,
            target_container_ptr,
        );
        self.mem_man.pagetable_map_4k_page(
            target_pcid,
            l4i,
            l3i,
            l2i,
            l1i,
            tagret_l1_p,
            &MapEntry { addr: new_page_ptr, write: true, execute_disable: false },
        );
        self.proc_man.set_container_mem_quota_mem_4k(target_container_ptr, old_quota - 1);
        
        MapEntry { addr: new_page_ptr, write: true, execute_disable: false }
    }

    pub fn alloc_and_map_io(
        &mut self,
        target_proc_ptr: ProcPtr,
        target_va: VAddr,
        tagret_l1_p: PageMapPtr,
    ) -> (ret: MapEntry)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(target_proc_ptr),
            old(self).get_proc_has_iommu_table(target_proc_ptr),
            old(self).get_container_quota(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).mem_4k >= 1,
            old(self).get_num_of_free_pages() >= 1,
            va_4k_valid(target_va),
            old(self).get_io_space(target_proc_ptr).dom().contains(target_va) == false,
            old(self).mem_man.get_iommu_table_by_ioid(
                old(self).get_proc(target_proc_ptr).ioid.unwrap(),
            ).unwrap().spec_resolve_mapping_l2(
                spec_va2index(target_va).0,
                spec_va2index(target_va).1,
                spec_va2index(target_va).2,
            ).is_Some(),
            old(self).mem_man.get_iommu_table_by_ioid(
                old(self).get_proc(target_proc_ptr).ioid.unwrap(),
            ).unwrap().spec_resolve_mapping_l2(
                spec_va2index(target_va).0,
                spec_va2index(target_va).1,
                spec_va2index(target_va).2,
            ).unwrap().addr == tagret_l1_p,
        ensures
            self.wf(),
            self.proc_dom() == old(self).proc_dom(),
            self.thread_dom() == old(self).thread_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - 1,
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) ==> self.get_address_space(p_ptr) =~= old(
                    self,
                ).get_address_space(p_ptr),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && self.get_proc_has_iommu_table(p_ptr) && p_ptr
                    != target_proc_ptr ==> self.get_io_space(p_ptr) =~= old(self).get_io_space(
                    p_ptr,
                ),
            forall|t_ptr: ThreadPtr|
                #![auto]
                self.thread_dom().contains(t_ptr) ==> self.get_thread(t_ptr) =~= old(
                    self,
                ).get_thread(t_ptr),
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(
                    target_proc_ptr,
                ).owning_container ==> self.get_container(c_ptr) =~= old(self).get_container(c_ptr)
                    && self.get_container_owned_pages(c_ptr) =~= old(
                    self,
                ).get_container_owned_pages(c_ptr),
            forall|e_ptr: EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
                    self,
                ).get_endpoint(e_ptr),
            forall|p: Pcid|
                #![trigger self.mem_man.pcid_active(p)]
                #![trigger self.mem_man.pcid_to_proc_ptr(p)]
                self.mem_man.pcid_active(p) ==> old(self).mem_man.pcid_to_proc_ptr(p)
                    == self.mem_man.pcid_to_proc_ptr(p),
            forall|i: IOid|
                #![trigger self.mem_man.ioid_active(i)]
                #![trigger self.mem_man.ioid_to_proc_ptr(i)]
                self.mem_man.ioid_active(i) ==> old(self).mem_man.ioid_to_proc_ptr(i)
                    == self.mem_man.ioid_to_proc_ptr(i),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_procs,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).parent_rev_ptr,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).children,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_endpoints,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_threads,
            // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
            // self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_cpus,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).scheduler,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).subtree_set
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).subtree_set,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).depth =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).depth,
            old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).quota.spec_subtract_mem_4k(
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).quota,
                1,
            ),
            self.get_io_space(target_proc_ptr) =~= old(self).get_io_space(target_proc_ptr).insert(
                target_va,
                ret,
            ),
    // old(self).page_alloc.page_is_mapped(ret.addr) == false,
    // self.page_alloc.page_is_mapped(ret.addr),
    // forall|p: PagePtr|
    //     #![trigger self.page_alloc.page_is_mapped(p)]
    //     p != ret.addr ==> self.page_alloc.page_is_mapped(p) == old(
    //         self,
    //     ).page_alloc.page_is_mapped(p),
    // self.page_mapping@.dom() == old(self).page_mapping@.dom().insert(ret.addr),
    // forall|page_ptr: PagePtr|
    //     #![trigger self.page_mapping@[page_ptr]]
    //     old(self).page_mapping@.dom().contains(page_ptr) ==> old(
    //         self,
    //     ).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
    // self.page_mapping@[ret.addr] == Set::empty().insert((target_proc_ptr, target_va)),

    {
        let target_container_ptr = self.proc_man.get_proc(target_proc_ptr).owning_container;
        let old_quota = self.proc_man.get_container(target_container_ptr).quota.mem_4k;
        let target_ioid = self.proc_man.get_proc(target_proc_ptr).ioid.unwrap();
        let (l4i, l3i, l2i, l1i) = va2index(target_va);
        let new_page_ptr = self.page_alloc.alloc_and_map_io_4k(
            target_ioid,
            target_va,
            target_container_ptr,
        );
        self.mem_man.iommu_table_map_4k_page(
            target_ioid,
            l4i,
            l3i,
            l2i,
            l1i,
            tagret_l1_p,
            &MapEntry { addr: new_page_ptr, write: true, execute_disable: false },
        );
        self.proc_man.set_container_mem_quota_mem_4k(target_container_ptr, old_quota - 1);
        MapEntry { addr: new_page_ptr, write: true, execute_disable: false }
    }

    pub fn create_entry_and_alloc_and_map(
        &mut self,
        target_proc_ptr: ProcPtr,
        target_va: VAddr,
    ) -> (ret: (usize, MapEntry))
        requires
            old(self).wf(),
            old(self).proc_dom().contains(target_proc_ptr),
            old(self).get_container_quota(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).mem_4k >= 4,
            old(self).get_num_of_free_pages() >= 4,
            va_4k_valid(target_va),
            old(self).get_address_space(target_proc_ptr).dom().contains(target_va) == false,
        ensures
            ret.0 <= 4,
            self.wf(),
            self.proc_dom() == old(self).proc_dom(),
            self.thread_dom() == old(self).thread_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - ret.0,
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && p_ptr != target_proc_ptr
                    ==> self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr),
            forall|t_ptr: ThreadPtr|
                #![auto]
                self.thread_dom().contains(t_ptr) ==> self.get_thread(t_ptr) =~= old(
                    self,
                ).get_thread(t_ptr),
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(
                    target_proc_ptr,
                ).owning_container ==> self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
            forall|e_ptr: EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
                    self,
                ).get_endpoint(e_ptr),
            forall|c: ContainerPtr|
                #![auto]
                self.container_dom().contains(c) && old(self).get_proc(
                    target_proc_ptr,
                ).owning_container != c ==> self.get_container_owned_pages(c) =~= old(
                    self,
                ).get_container_owned_pages(c),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_procs,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).parent_rev_ptr,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).children,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_endpoints,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_threads,
            // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
            // self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_cpus,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).scheduler,
            old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).quota.spec_subtract_mem_4k(
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).quota,
                ret.0,
            ),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).subtree_set
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).subtree_set,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).depth =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).depth,
            self.get_address_space(target_proc_ptr).dom() =~= old(self).get_address_space(
                target_proc_ptr,
            ).dom().insert(target_va),
            self.get_address_space(target_proc_ptr) =~= old(self).get_address_space(
                target_proc_ptr,
            ).insert(target_va, ret.1),
            old(self).page_alloc.page_is_mapped(ret.1.addr) == false,
            self.page_alloc.page_is_mapped(ret.1.addr),
            forall|p: PagePtr|
                #![trigger self.page_alloc.page_is_mapped(p)]
                p != ret.1.addr ==> self.page_alloc.page_is_mapped(p) == old(
                    self,
                ).page_alloc.page_is_mapped(p),
            self.page_mapping@.dom() == old(self).page_mapping@.dom().insert(ret.1.addr),
            forall|page_ptr: PagePtr|
                #![trigger self.page_mapping@[page_ptr]]
                old(self).page_mapping@.dom().contains(page_ptr) ==> old(
                    self,
                ).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
            self.page_mapping@[ret.1.addr] == Set::empty().insert((target_proc_ptr, target_va)),
    {
        let (ret, new_entry) = self.create_entry(target_proc_ptr, target_va);
        (ret + 1, self.alloc_and_map(target_proc_ptr, target_va, new_entry))
    }

    pub fn create_entry_and_alloc_and_map_io(
        &mut self,
        target_proc_ptr: ProcPtr,
        target_va: VAddr,
    ) -> (ret: (usize, MapEntry))
        requires
            old(self).wf(),
            old(self).proc_dom().contains(target_proc_ptr),
            old(self).get_proc_has_iommu_table(target_proc_ptr),
            old(self).get_container_quota(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).mem_4k >= 4,
            old(self).get_num_of_free_pages() >= 4,
            va_4k_valid(target_va),
            old(self).get_io_space(target_proc_ptr).dom().contains(target_va) == false,
        ensures
            ret.0 <= 4,
            self.wf(),
            self.proc_dom() == old(self).proc_dom(),
            self.thread_dom() == old(self).thread_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - ret.0,
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) ==> self.get_address_space(p_ptr) =~= old(
                    self,
                ).get_address_space(p_ptr),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && p_ptr != target_proc_ptr
                    && self.get_proc_has_iommu_table(p_ptr) ==> self.get_io_space(p_ptr) =~= old(
                    self,
                ).get_io_space(p_ptr),
            forall|t_ptr: ThreadPtr|
                #![auto]
                self.thread_dom().contains(t_ptr) ==> self.get_thread(t_ptr) =~= old(
                    self,
                ).get_thread(t_ptr),
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(
                    target_proc_ptr,
                ).owning_container ==> self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
            forall|e_ptr: EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
                    self,
                ).get_endpoint(e_ptr),
            forall|c: ContainerPtr|
                #![auto]
                self.container_dom().contains(c) && old(self).get_proc(
                    target_proc_ptr,
                ).owning_container != c ==> self.get_container_owned_pages(c) =~= old(
                    self,
                ).get_container_owned_pages(c),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_procs,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).parent,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).parent_rev_ptr
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).parent_rev_ptr,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).children
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).children,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_endpoints,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_threads,
            // self.get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota =~= old(self).get_container(old(self).get_proc(proc_ptr).owning_container).mem_quota,
            // self.get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_proc(target_proc_ptr).owning_container).mem_used,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_cpus
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_cpus,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).scheduler
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).scheduler,
            old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).quota.spec_subtract_mem_4k(
                self.get_container(old(self).get_proc(target_proc_ptr).owning_container).quota,
                ret.0,
            ),
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).subtree_set
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).subtree_set,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).depth =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).depth,
            self.get_io_space(target_proc_ptr).dom() =~= old(self).get_io_space(
                target_proc_ptr,
            ).dom().insert(target_va),
            self.get_io_space(target_proc_ptr) =~= old(self).get_io_space(target_proc_ptr).insert(
                target_va,
                ret.1,
            ),
    // old(self).page_alloc.page_is_mapped(ret.1.addr) == false,
    // self.page_alloc.page_is_mapped(ret.1.addr),
    // forall|p: PagePtr|
    //     #![trigger self.page_alloc.page_is_mapped(p)]
    //     p != ret.1.addr ==> self.page_alloc.page_is_mapped(p) == old(
    //         self,
    //     ).page_alloc.page_is_mapped(p),
    // self.page_mapping@.dom() == old(self).page_mapping@.dom().insert(ret.1.addr),
    // forall|page_ptr: PagePtr|
    //     #![trigger self.page_mapping@[page_ptr]]
    //     old(self).page_mapping@.dom().contains(page_ptr) ==> old(
    //         self,
    //     ).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
    // self.page_mapping@[ret.1.addr] == Set::empty().insert((target_proc_ptr, target_va)),

    {
        let (ret, new_entry) = self.create_iommu_table_entry(target_proc_ptr, target_va);
        (ret + 1, self.alloc_and_map_io(target_proc_ptr, target_va, new_entry))
    }

    pub fn range_alloc_and_map(&mut self, target_proc_ptr: ProcPtr, va_range: &VaRange4K) -> (ret: (
        usize,
        Ghost<Seq<PagePtr>>,
    ))
        requires
            old(self).wf(),
            old(self).proc_dom().contains(target_proc_ptr),
            va_range.wf(),
            old(self).get_container_quota(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).mem_4k >= 4 * va_range.len,
            old(self).get_num_of_free_pages() >= 4 * va_range.len,
            forall|i: int|
                #![auto]
                0 <= i < va_range.len ==> old(self).get_address_space(
                    target_proc_ptr,
                ).dom().contains(va_range@[i]) == false,
            va_range.len * 4 < usize::MAX,
        ensures
            self.wf(),
            self.proc_dom() == old(self).proc_dom(),
            self.thread_dom() == old(self).thread_dom(),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom(),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) && p_ptr != target_proc_ptr
                    ==> self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr),
            forall|p_ptr: ProcPtr|
                #![auto]
                self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
                    p_ptr,
                ),
            forall|t_ptr: ThreadPtr|
                #![auto]
                self.thread_dom().contains(t_ptr) ==> self.get_thread(t_ptr) =~= old(
                    self,
                ).get_thread(t_ptr),
            forall|c_ptr: ContainerPtr|
                #![auto]
                self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(
                    target_proc_ptr,
                ).owning_container ==> self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
            forall|e_ptr: EndpointPtr|
                #![auto]
                self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
                    self,
                ).get_endpoint(e_ptr),
            forall|c: ContainerPtr|
                #![auto]
                self.container_dom().contains(c) && old(self).get_proc(
                    target_proc_ptr,
                ).owning_container != c ==> self.get_container_owned_pages(c) =~= old(
                    self,
                ).get_container_owned_pages(c),
            forall|j: usize|
                #![auto]
                0 <= j < va_range.len ==> self.get_address_space(target_proc_ptr).dom().contains(
                    va_range@[j as int],
                ),
            ret.1@.len() == va_range.len,
            forall|j: usize|
                #![auto]
                0 <= j < va_range.len ==> self.get_address_space(
                    target_proc_ptr,
                )[va_range@[j as int]].addr == ret.1@[j as int],
            forall|p: PagePtr|
                #![trigger self.page_alloc.page_is_mapped(p)]
                ret.1@.contains(p) == false ==> self.page_alloc.page_is_mapped(p) == old(
                    self,
                ).page_alloc.page_is_mapped(p),
            va_range.len == ret.1@.len(),
            forall|j: usize|
                #![auto]
                0 <= j < va_range.len ==> old(self).page_alloc.page_is_mapped(ret.1@[j as int])
                    == false,
            forall|j: usize|
                #![auto]
                0 <= j < va_range.len ==> self.page_alloc.page_is_mapped(ret.1@[j as int]) == true,
            self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - ret.0,
            old(self).get_container_quota(
                self.get_proc(target_proc_ptr).owning_container,
            ).spec_subtract_mem_4k(
                self.get_container_quota(self.get_proc(target_proc_ptr).owning_container),
                ret.0,
            ),
            forall|va: VAddr|
                #![trigger self.get_address_space(target_proc_ptr).dom().contains(va)]
                #![trigger self.get_address_space(target_proc_ptr)[va]]
            // #![trigger va_4k_valid(va)]
            // va_4k_valid(va)
            // &&

                va_range@.contains(va) == false ==> self.get_address_space(
                    target_proc_ptr,
                ).dom().contains(va) == old(self).get_address_space(target_proc_ptr).dom().contains(
                    va,
                ) && self.get_address_space(target_proc_ptr)[va] == old(self).get_address_space(
                    target_proc_ptr,
                )[va],
            forall|va: VAddr|
                #![trigger self.get_address_space(target_proc_ptr).dom().contains(va)]
            // #![trigger va_4k_valid(va)]
            // va_4k_valid(va)
            // &&

                va_range@.contains(va) ==> self.get_address_space(target_proc_ptr).dom().contains(
                    va,
                ),
            self.page_mapping@.dom() == old(self).page_mapping@.dom() + ret.1@.to_set(),
            forall|page_ptr: PagePtr|
                #![trigger self.page_mapping@[page_ptr]]
                old(self).page_mapping@.dom().contains(page_ptr) ==> old(
                    self,
                ).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
            forall|i: usize|
                #![auto]
                0 <= i < va_range.len ==> self.page_mapping@[ret.1@[i as int]]
                    == Set::empty().insert((target_proc_ptr, va_range@[i as int])),
            forall|va: VAddr|
                #![auto]
                va_range@.contains(va) == false ==> self.get_address_space(target_proc_ptr)[va]
                    =~= old(self).get_address_space(target_proc_ptr)[va],
            forall|i: usize|
                #![auto]
                0 <= i < va_range.len ==> self.get_address_space(
                    target_proc_ptr,
                )[va_range@[i as int]].addr == ret.1@[i as int],
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_procs,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_threads,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).owned_endpoints,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).subtree_set
                =~= old(self).get_container(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).subtree_set,
            self.get_container(old(self).get_proc(target_proc_ptr).owning_container).depth =~= old(
                self,
            ).get_container(old(self).get_proc(target_proc_ptr).owning_container).depth,
    {
        let mut num_page: usize = 0;
        let mut page_diff: Ghost<Seq<PagePtr>> = Ghost(Seq::empty());
        for i in 0..va_range.len
        {
            let (num, map_entry) = self.create_entry_and_alloc_and_map(
                target_proc_ptr,
                va_range.index(i),
            );

            num_page = num_page + num;
        }
        (num_page, page_diff)
    }

    pub fn range_alloc_and_map_io(
        &mut self,
        target_proc_ptr: ProcPtr,
        va_range: &VaRange4K,
    ) -> (ret: (usize, Ghost<Seq<PagePtr>>))
        requires
            old(self).wf(),
            old(self).proc_dom().contains(target_proc_ptr),
            old(self).get_proc_has_iommu_table(target_proc_ptr),
            va_range.wf(),
            old(self).get_container_quota(
                old(self).get_proc(target_proc_ptr).owning_container,
            ).mem_4k >= 4 * va_range.len,
            old(self).get_num_of_free_pages() >= 4 * va_range.len,
            forall|i: int|
                #![auto]
                0 <= i < va_range.len ==> old(self).get_io_space(target_proc_ptr).dom().contains(
                    va_range@[i],
                ) == false,
            va_range.len * 4 < usize::MAX,
        ensures
            self.wf(),
    // self.proc_dom() == old(self).proc_dom(),
    // self.thread_dom() == old(self).thread_dom(),
    // self.endpoint_dom() == old(self).endpoint_dom(),
    // self.container_dom() == old(self).container_dom(),
    // forall|p_ptr: ProcPtr|
    //     #![auto]
    //     self.proc_dom().contains(p_ptr) && p_ptr != target_proc_ptr &&
    //         self.get_proc_has_iommu_table(p_ptr)
    //         ==> self.get_io_space(p_ptr) =~= old(self).get_io_space(p_ptr),
    // forall|p_ptr: ProcPtr|
    //     #![auto]
    //     self.proc_dom().contains(p_ptr)
    //         ==> self.get_address_space(p_ptr) =~= old(self).get_address_space(p_ptr),
    // forall|p_ptr: ProcPtr|
    //     #![auto]
    //     self.proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(self).get_proc(
    //         p_ptr,
    //     ),
    // forall|t_ptr: ThreadPtr|
    //     #![auto]
    //     self.thread_dom().contains(t_ptr) ==> self.get_thread(t_ptr) =~= old(
    //         self,
    //     ).get_thread(t_ptr),
    // forall|c_ptr: ContainerPtr|
    //     #![auto]
    //     self.container_dom().contains(c_ptr) && c_ptr != self.get_proc(
    //         target_proc_ptr,
    //     ).owning_container ==> self.get_container(c_ptr) =~= old(self).get_container(c_ptr),
    // forall|e_ptr: EndpointPtr|
    //     #![auto]
    //     self.endpoint_dom().contains(e_ptr) ==> self.get_endpoint(e_ptr) =~= old(
    //         self,
    //     ).get_endpoint(e_ptr),
    // forall|c: ContainerPtr|
    //     #![auto]
    //     self.container_dom().contains(c) && old(self).get_proc(
    //         target_proc_ptr,
    //     ).owning_container != c ==> self.get_container_owned_pages(c) =~= old(
    //         self,
    //     ).get_container_owned_pages(c),
    // forall|j: usize|
    //     #![auto]
    //     0 <= j < va_range.len ==> self.get_io_space(target_proc_ptr).dom().contains(
    //         va_range@[j as int],
    //     ),
    // ret.1@.len() == va_range.len,
    // forall|j: usize|
    //     #![auto]
    //     0 <= j < va_range.len ==> self.get_io_space(
    //         target_proc_ptr,
    //     )[va_range@[j as int]].addr == ret.1@[j as int],
    // forall|p: PagePtr|
    //     #![trigger self.page_alloc.page_is_mapped(p)]
    //     ret.1@.contains(p) == false ==> self.page_alloc.page_is_mapped(p) == old(
    //         self,
    //     ).page_alloc.page_is_mapped(p),
    // va_range.len == ret.1@.len(),
    // forall|j: usize|
    //     #![auto]
    //     0 <= j < va_range.len ==> old(self).page_alloc.page_is_mapped(ret.1@[j as int])
    //         == false,
    // forall|j: usize|
    //     #![auto]
    //     0 <= j < va_range.len ==> self.page_alloc.page_is_mapped(ret.1@[j as int]) == true,
    // self.get_num_of_free_pages() == old(self).get_num_of_free_pages() - ret.0,
    // old(self).get_container_quota(
    //     self.get_proc(target_proc_ptr).owning_container,
    // ).spec_subtract_mem_4k(
    //     self.get_container_quota(self.get_proc(target_proc_ptr).owning_container),
    //     ret.0,
    // ),
    // forall|va: VAddr|
    //     #![trigger self.get_io_space(target_proc_ptr).dom().contains(va)]
    //     #![trigger self.get_io_space(target_proc_ptr)[va]]
    // // #![trigger va_4k_valid(va)]
    // // va_4k_valid(va)
    // // &&
    //     va_range@.contains(va) == false ==> self.get_io_space(
    //         target_proc_ptr,
    //     ).dom().contains(va) == old(self).get_io_space(target_proc_ptr).dom().contains(
    //         va,
    //     ) && self.get_io_space(target_proc_ptr)[va] == old(self).get_io_space(
    //         target_proc_ptr,
    //     )[va],
    // forall|va: VAddr|
    //     #![trigger self.get_io_space(target_proc_ptr).dom().contains(va)]
    // // #![trigger va_4k_valid(va)]
    // // va_4k_valid(va)
    // // &&
    //     va_range@.contains(va) ==> self.get_io_space(target_proc_ptr).dom().contains(
    //         va,
    //     ),
    // self.page_mapping@.dom() == old(self).page_mapping@.dom() + ret.1@.to_set(),
    // forall|page_ptr: PagePtr|
    //     #![trigger self.page_mapping@[page_ptr]]
    //     old(self).page_mapping@.dom().contains(page_ptr) ==> old(
    //         self,
    //     ).page_mapping@[page_ptr] == self.page_mapping@[page_ptr],
    // forall|i: usize|
    //     #![auto]
    //     0 <= i < va_range.len ==> self.page_mapping@[ret.1@[i as int]]
    //         == Set::empty().insert((target_proc_ptr, va_range@[i as int])),
    // forall|va: VAddr|
    //     #![auto]
    //     va_range@.contains(va) == false ==> self.get_io_space(target_proc_ptr)[va]
    //         =~= old(self).get_io_space(target_proc_ptr)[va],
    // forall|i: usize|
    //     #![auto]
    //     0 <= i < va_range.len ==> self.get_io_space(
    //         target_proc_ptr,
    //     )[va_range@[i as int]].addr == ret.1@[i as int],
    // self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_procs
    //     =~= old(self).get_container(
    //     old(self).get_proc(target_proc_ptr).owning_container,
    // ).owned_procs,
    // self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_threads
    //     =~= old(self).get_container(
    //     old(self).get_proc(target_proc_ptr).owning_container,
    // ).owned_threads,
    // self.get_container(old(self).get_proc(target_proc_ptr).owning_container).owned_endpoints
    //     =~= old(self).get_container(
    //     old(self).get_proc(target_proc_ptr).owning_container,
    // ).owned_endpoints,
    // self.get_container(old(self).get_proc(target_proc_ptr).owning_container).subtree_set
    //     =~= old(self).get_container(
    //     old(self).get_proc(target_proc_ptr).owning_container,
    // ).subtree_set,
    // self.get_container(old(self).get_proc(target_proc_ptr).owning_container).depth =~= old(
    //     self,
    // ).get_container(old(self).get_proc(target_proc_ptr).owning_container).depth,

    {
        let mut num_page: usize = 0;
        let mut page_diff: Ghost<Seq<PagePtr>> = Ghost(Seq::empty());
        for i in 0..va_range.len
        {
            let (num, map_entry) = self.create_entry_and_alloc_and_map_io(
                target_proc_ptr,
                va_range.index(i),
            );

            num_page = num_page + num;
            
        }
        (num_page, page_diff)
    }
}

} // verus!
