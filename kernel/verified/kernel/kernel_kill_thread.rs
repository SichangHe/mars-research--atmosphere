use vstd::prelude::*;
verus! {
use crate::define::*;
use crate::kernel::Kernel;
use crate::va_range::*;
use crate::process_manager::spec_util::*;
use crate::process_manager::spec_proof::*;
impl Kernel {
    pub fn kernel_kill_thread(&mut self, thread_ptr: ThreadPtr)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
        ensures
            self.wf(),
            self.thread_dom() == old(self).thread_dom().remove(thread_ptr),
            threads_unchanged_except(old(self).proc_man, self.proc_man, set![]),
            self.proc_dom() == old(self).proc_dom(),
            process_tree_unchanged(old(self).proc_man, self.proc_man),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(old(self).proc_man, self.proc_man),
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@ == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads@.remove_value(thread_ptr), 
            self.get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() == 
              old(self).get_proc(old(self).get_thread(thread_ptr).owning_proc).owned_threads.len() - 1,  
    {

        let thread_state = self.proc_man.get_thread(thread_ptr).state;
        let blocking_endpoint_index = self.proc_man.get_thread(thread_ptr).blocking_endpoint_index;

        for i in 0..MAX_NUM_ENDPOINT_DESCRIPTORS
        {
            match thread_state {
                ThreadState::BLOCKED => {
                    if blocking_endpoint_index.unwrap() != i {
                        self.kernel_drop_endpoint(thread_ptr, i);
                    }
                },
                _ => {
                    self.kernel_drop_endpoint(thread_ptr, i);
                }
            }
        }

        match self.proc_man.get_thread(thread_ptr).state {
            ThreadState::SCHEDULED => {
                let (page_ptr, page_perm) = self.proc_man.kill_scheduled_thread(thread_ptr);
                self.page_alloc.free_page_4k(page_ptr, page_perm);
            },
            ThreadState::BLOCKED => {
                let ((page_ptr, page_perm), page_op) = self.proc_man.kill_blocked_thread(thread_ptr);
                self.page_alloc.free_page_4k(page_ptr, page_perm);
                if let Some((page_ptr2, page_perm2)) = page_op{
                    self.page_alloc.free_page_4k(page_ptr2, page_perm2);
                }
            },
            ThreadState::RUNNING => {
                let (page_ptr, page_perm) = self.proc_man.kill_running_thread(thread_ptr);
                self.page_alloc.free_page_4k(page_ptr, page_perm);
            },
        
        }
    }

    pub fn kernel_proc_kill_all_threads(&mut self, proc_ptr: ProcPtr)
        requires
            old(self).wf(),
            old(self).proc_dom().contains(proc_ptr),
        ensures
            self.wf(),
            self.proc_dom().contains(proc_ptr),
            self.get_proc(proc_ptr).owned_threads.len() == 0,

            self.proc_dom() == old(self).proc_dom(),
            process_tree_unchanged(old(self).proc_man, self.proc_man),
            self.container_dom() == old(self).container_dom(),
            containers_tree_unchanged(old(self).proc_man, self.proc_man),
    {
        let num_threads = self.proc_man.get_proc(proc_ptr).owned_threads.len();
        for i in 0..num_threads
        {
            let thread_ptr = self.proc_man.get_proc(proc_ptr).owned_threads.get_head();
            self.kernel_kill_thread(thread_ptr);
        }

    }
}

}