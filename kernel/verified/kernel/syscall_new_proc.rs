use vstd::prelude::*;
verus! {

// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_proof::*;
// use crate::util::page_ptr_util_u::*;
// use crate::lemma::lemma_t::set_lemma;
use crate::lemma::lemma_u::*;

// use crate::util::page_ptr_util_u::*;
use crate::define::*;

// use crate::trap::*;
// use crate::pagetable::pagemap_util_t::*;
// use crate::pagetable::entry::*;
use crate::kernel::Kernel;
use crate::va_range::VaRange4K;
use crate::trap::Registers;

//use crate::pagetable::pagemap_util_t::*;
pub open spec fn syscall_new_proc_with_endpoint_requirement(
    old: Kernel,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    pt_regs: Registers,
    va_range: VaRange4K,
) -> bool {
    let proc_ptr = old.get_thread(thread_ptr).owning_proc;
    let pcid = old.get_proc(proc_ptr).pcid;
    let container_ptr = old.get_thread(thread_ptr).owning_container;
    if old.get_is_process_childern_list_full(proc_ptr) {
        false
    } else if old.get_is_process_depth_overflow(proc_ptr) {
        false
    } else if old.get_container_quota(container_ptr).mem_4k < va_range.len * 3 + 2 {
        false
    } else if old.get_is_scheduler_full(container_ptr) {
        false
    } else if old.get_is_proc_list_full(container_ptr) {
        false
    } else if old.get_num_of_free_pages() < va_range.len * 3 + 2 {
        false
    } else if old.get_is_pcid_exhausted() {
        false
    } else if old.get_endpoint_shareable(thread_ptr, endpoint_index) == false {
        false
    } else if old.address_space_range_shareable(proc_ptr, &va_range) == false {
        false
    } else {
        true
    }
}

pub open spec fn syscall_new_proc_with_endpoint_spec(
    old: Kernel,
    new: Kernel,
    thread_ptr: ThreadPtr,
    endpoint_index: EndpointIdx,
    pt_regs: Registers,
    va_range: VaRange4K,
    ret: SyscallReturnStruct,
) -> bool {
    let proc_ptr = old.get_thread(thread_ptr).owning_proc;
    let pcid = old.get_proc(proc_ptr).pcid;
    let container_ptr = old.get_thread(thread_ptr).owning_container;
    let endpoint_ptr = old.get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap();
    let (new_proc_ptr, new_thread_ptr) = ret.get_return_vaule_pair_usize().unwrap();

    &&& syscall_new_proc_with_endpoint_requirement(
        old,
        thread_ptr,
        endpoint_index,
        pt_regs,
        va_range,
    ) == false ==> old == new
    &&& syscall_new_proc_with_endpoint_requirement(
        old,
        thread_ptr,
        endpoint_index,
        pt_regs,
        va_range,
    ) ==>
    // things that did not change
    old.container_dom() =~= new.container_dom() && old.endpoint_dom() =~= new.endpoint_dom()
        && forall|t_ptr: ThreadPtr|
        #![trigger new.get_thread(t_ptr)]
        old.thread_dom().contains(t_ptr) ==> new.get_thread(t_ptr) =~= old.get_thread(t_ptr)
            && forall|p_ptr: ProcPtr|
            #![trigger new.get_proc(p_ptr)]
            old.proc_dom().contains(p_ptr) && old.get_container(
                container_ptr,
            ).owned_procs@.contains(p_ptr) == false ==> old.get_proc(p_ptr) =~= new.get_proc(p_ptr)
                && forall|p_ptr: ProcPtr|
                #![trigger new.get_proc(p_ptr)]
                old.proc_dom().contains(p_ptr) ==> old.get_proc(p_ptr).owned_threads
                    =~= new.get_proc(p_ptr).owned_threads && forall|c: ContainerPtr|
                    #![trigger new.get_container_owned_pages(c)]
                    new.container_dom().contains(c) && c != container_ptr ==> old.get_container(c)
                        =~= new.get_container(c) && forall|e_ptr: EndpointPtr|
                        #![trigger new.get_endpoint(e_ptr)]
                        new.endpoint_dom().contains(e_ptr) && e_ptr != endpoint_ptr
                            ==> old.get_endpoint(e_ptr) =~= new.get_endpoint(e_ptr) && forall|
                            c: ContainerPtr,
                        |
                            #![trigger new.get_container_owned_pages(c)]
                            new.container_dom().contains(c) ==> old.get_container_owned_pages(c)
                                =~= new.get_container_owned_pages(c) && forall|p_ptr: ProcPtr|
                                #![trigger new.get_address_space(p_ptr)]
                                old.proc_dom().contains(p_ptr) ==> new.get_address_space(p_ptr)
                                    =~= old.get_address_space(p_ptr) && new.get_container(
                                    container_ptr,
                                ).owned_endpoints@ =~= old.get_container(
                                    container_ptr,
                                ).owned_endpoints@ && new.get_physical_page_mapping().dom()
                                    =~= old.get_physical_page_mapping().dom() && forall|
                                    page_ptr: PagePtr,
                                |
                                    #![trigger new.get_physical_page_mapping()[page_ptr]]
                                    old.get_physical_page_mapping().dom().contains(page_ptr) && (
                                    forall|i: int|
                                        #![auto]
                                        0 <= i < va_range.len ==> old.get_address_space(
                                            proc_ptr,
                                        )[va_range@[i]].addr != page_ptr)
                                        ==> old.get_physical_page_mapping()[page_ptr]
                                        == new.get_physical_page_mapping()[page_ptr]
                                    // things that changed
                                     && old.proc_dom().insert(new_proc_ptr) =~= new.proc_dom()
                                        && old.thread_dom().insert(new_thread_ptr)
                                        =~= new.thread_dom() && new.get_proc(
                                        new_proc_ptr,
                                    ).owned_threads@ =~= Seq::<ThreadPtr>::empty().push(
                                        new_thread_ptr,
                                    ) && new.get_proc(new_proc_ptr).owning_container
                                        == container_ptr && new.get_container(
                                        container_ptr,
                                    ).owned_threads@ =~= old.get_container(
                                        container_ptr,
                                    ).owned_threads@.insert(new_thread_ptr) && new.get_container(
                                        container_ptr,
                                    ).owned_procs@ =~= old.get_container(
                                        container_ptr,
                                    ).owned_procs@.push(new_proc_ptr) && new.get_thread(
                                        new_thread_ptr,
                                    ).owning_container == container_ptr && new.get_thread(
                                        new_thread_ptr,
                                    ).endpoint_descriptors@ =~= Seq::new(
                                        MAX_NUM_ENDPOINT_DESCRIPTORS as nat,
                                        |i: int| { None },
                                    ).update(0, Some(endpoint_ptr)) && new.get_endpoint(
                                        endpoint_ptr,
                                    ).owning_threads@ =~= old.get_endpoint(
                                        endpoint_ptr,
                                    ).owning_threads@.insert((new_thread_ptr, 0)) && (forall|
                                        page_ptr: PagePtr,
                                    |
                                        #![trigger new.get_physical_page_mapping()[page_ptr]]
                                        old.get_physical_page_mapping().dom().contains(page_ptr)
                                            && new.get_physical_page_mapping()[page_ptr]
                                            != old.get_physical_page_mapping()[page_ptr] ==> (
                                        forall|p_ptr: Pcid, va: VAddr|
                                            #![auto]
                                            new.get_physical_page_mapping()[page_ptr].contains(
                                                (p_ptr, va),
                                            )
                                                && !old.get_physical_page_mapping()[page_ptr].contains(
                                            (p_ptr, va)) ==> p_ptr == new_proc_ptr
                                                && va_range@.contains(va))) && forall|i: int|
                                        #![auto]
                                        0 <= i < va_range.len ==> new.get_address_space(
                                            new_proc_ptr,
                                        ).dom().contains(va_range@[i]) && new.get_address_space(
                                            new_proc_ptr,
                                        )[va_range@[i]] == old.get_address_space(
                                            proc_ptr,
                                        )[va_range@[i]] && forall|va: VAddr|
                                            #![auto]
                                            va_range@.contains(va) == false
                                                ==> new.get_address_space(
                                                new_proc_ptr,
                                            ).dom().contains(va) == false
}

impl Kernel {
    pub fn syscall_new_proc_with_endpoint(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        pt_regs: &Registers,
        va_range: VaRange4K,
    ) -> (ret: SyscallReturnStruct)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            va_range.wf(),
            va_range.len * 3 + 3 < usize::MAX,
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
        ensures
            syscall_new_proc_with_endpoint_requirement(
                *old(self),
                thread_ptr,
                endpoint_index,
                *pt_regs,
                va_range,
            ) == false <==> ret.is_error(),
            syscall_new_proc_with_endpoint_spec(
                *old(self),
                *self,
                thread_ptr,
                endpoint_index,
                *pt_regs,
                va_range,
                ret,
            ),
    {
        let proc_ptr = self.proc_man.get_thread(thread_ptr).owning_proc;
        let pcid = self.proc_man.get_proc(proc_ptr).pcid;
        let container_ptr = self.proc_man.get_thread(thread_ptr).owning_container;

        if self.proc_man.get_proc(proc_ptr).children.len() >= PROC_CHILD_LIST_LEN {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_proc(proc_ptr).depth >= usize::MAX {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container(container_ptr).quota.mem_4k < va_range.len * 3 + 2 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container(container_ptr).scheduler.len()
            >= MAX_CONTAINER_SCHEDULER_LEN {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.proc_man.get_container(container_ptr).owned_procs.len() >= CONTAINER_PROC_LIST_LEN {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.page_alloc.free_pages_4k.len() < va_range.len * 3 + 2 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.mem_man.free_pcids.len() < 1 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let endpoint_ptr_op = self.proc_man.get_endpoint_ptr_by_endpoint_idx(
            thread_ptr,
            endpoint_index,
        );
        if endpoint_ptr_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let endpoint_ptr = endpoint_ptr_op.unwrap();
        if self.proc_man.get_endpoint(endpoint_ptr).rf_counter == usize::MAX {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.check_address_space_va_range_shareable(proc_ptr, &va_range) == false {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }

        let (page_ptr_2, page_perm_2) = self.page_alloc.alloc_page_4k();
        let (page_ptr_3, page_perm_3) = self.page_alloc.alloc_page_4k();

        let new_pcid = self.mem_man.alloc_page_table(page_ptr_2);
        self.proc_man.new_proc_with_endpoint(
            thread_ptr,
            endpoint_index,
            pt_regs,
            page_ptr_2,
            page_perm_2,
            page_ptr_3,
            page_perm_3,
            new_pcid,
        );

        self.range_create_and_share_mapping(proc_ptr, &va_range, page_ptr_2, &va_range);

        return SyscallReturnStruct::NoSwitchNew(
            RetValueType::SuccessPairUsize { value1: page_ptr_2, value2: page_ptr_3 },
        );
    }
}

} // verus!
