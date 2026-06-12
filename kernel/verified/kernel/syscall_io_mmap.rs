use vstd::prelude::*;
verus! {

// use crate::allocator::page_allocator_spec_impl::*;
// use crate::memory_manager::spec_impl::*;
// use crate::process_manager::spec_proof::*;
// use crate::util::page_ptr_util_u::*;
// use crate::lemma::lemma_t::set_lemma;
// use crate::lemma::lemma_u::*;
// use crate::util::page_ptr_util_u::*;
use crate::define::*;

// use crate::trap::*;
// use crate::pagetable::pagemap_util_t::*;
// use crate::pagetable::entry::*;
use crate::kernel::Kernel;
use crate::va_range::VaRange4K;

impl Kernel {
    pub fn syscall_io_mmap(&mut self, thread_ptr: ThreadPtr, va_range: VaRange4K) -> (ret:
        SyscallReturnStruct)
        requires
            old(self).total_wf(),
            old(self).thread_dom().contains(thread_ptr),
            va_range.wf(),
            va_range.len * 4 < usize::MAX,
    {
        let proc_ptr = self.proc_man.get_thread(thread_ptr).owning_proc;
        let ioid_op = self.proc_man.get_proc(proc_ptr).ioid;
        let container_ptr = self.proc_man.get_proc(proc_ptr).owning_container;

        if ioid_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }

        let ioid = ioid_op.unwrap();

        if self.proc_man.get_container(container_ptr).quota.mem_4k < va_range.len * 4 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::ErrorNoQuota);
        }

        if self.check_io_space_va_range_free(proc_ptr, &va_range) == false {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::ErrorVaInUse);
        }
        let (num_page, seq_pages) = self.range_alloc_and_map_io(proc_ptr, &va_range);

        return SyscallReturnStruct::NoSwitchNew(RetValueType::SuccessSeqUsize { value: seq_pages });
    }

     pub fn syscall_mmap_to_iommu_table(&mut self, thread_ptr: ThreadPtr, va_range: VaRange4K) -> (ret:
        SyscallReturnStruct)
        requires
            old(self).total_wf(),
            old(self).thread_dom().contains(thread_ptr),
            va_range.wf(),
            va_range.len * 4 < usize::MAX,
    {
        assume(false);
        let proc_ptr = self.proc_man.get_thread(thread_ptr).owning_proc;
        let pcid = self.proc_man.get_proc(proc_ptr).pcid;
        let ioid_op = self.proc_man.get_proc(proc_ptr).ioid;
        let container_ptr = self.proc_man.get_proc(proc_ptr).owning_container;

        proof {
            self.proc_man.thread_inv();
            self.proc_man.process_inv();
        }

        if ioid_op.is_none() {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let ioid = ioid_op.unwrap();

        if self.proc_man.get_container(container_ptr).quota.mem_4k < va_range.len * 4 {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        assert(self.page_alloc.free_pages_4k.len() >= va_range.len * 4) by {
            old(self).fold_mem_4k_lemma();
        }
        if !self.check_address_space_va_range_shareable(proc_ptr, &va_range){
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        if self.check_io_space_va_range_free(proc_ptr, &va_range) == false {
            return SyscallReturnStruct::NoSwitchNew(RetValueType::Error);
        }
        let num_page = self.range_create_and_share_mapping_to_iommu_table(proc_ptr, &va_range);


        return SyscallReturnStruct::NoSwitchNew(RetValueType::SuccessUsize { value: num_page });
    }
}

} // verus!
