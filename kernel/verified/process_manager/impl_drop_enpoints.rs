use vstd::prelude::*;

use crate::process_manager::endpoint;
verus! {

use crate::define::*;
use vstd::simple_pptr::PointsTo;
use crate::trap::*;
use crate::array::Array;
use crate::process_manager::endpoint::*;
use crate::process_manager::process::*;
use crate::process_manager::container::*;
use crate::process_manager::thread::*;
use crate::process_manager::cpu::*;
use vstd::simple_pptr::PPtr;
use crate::process_manager::thread_util_t::*;
use crate::process_manager::proc_util_t::*;
use crate::process_manager::container_util_t::*;
use crate::process_manager::endpoint_util_t::*;
use crate::lemma::lemma_u::*;
use crate::lemma::lemma_t::*;
use crate::array_set::ArraySet;
use core::mem::MaybeUninit;
use crate::trap::Registers;
use crate::process_manager::container_tree::*;
use crate::process_manager::process_tree::*;
use crate::process_manager::spec_proof::*;
use crate::process_manager::spec_util::*;

impl ProcessManager {
    pub fn drop_endpoint(
        &mut self,
        thread_ptr: ThreadPtr,
        edp_idx: EndpointIdx
    ) -> (ret: Option<(PagePtr, Tracked<PagePerm4k>)>)
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            0 <= edp_idx < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_thread(thread_ptr).state == ThreadState::BLOCKED
            ==>
                old(self).get_thread(thread_ptr).blocking_endpoint_index.unwrap() != edp_idx,
        ensures
            self.wf(),
            ret.is_Some() ==> self.page_closure() =~= old(self).page_closure().remove(ret.unwrap().0),
            ret.is_Some() ==> old(self).page_closure().contains(ret.unwrap().0),
            ret.is_Some() ==> ret.unwrap().0 == ret.unwrap().1@.addr(),
            ret.is_Some() ==> ret.unwrap().1@.is_init(),
            ret.is_Some() ==> old(self).container_dom().contains(ret.unwrap().0) == false,
            ret.is_None() ==> self.page_closure() =~= old(self).page_closure(),
            ret.is_None() ==> containers_unchanged(*old(self), *self),
            ret.is_Some() ==> {
                &&&
                containers_unchanged_except(*old(self), *self, set![old(self).get_endpoint(old(self).get_thread(thread_ptr).endpoint_descriptors[edp_idx as int].unwrap()).owning_container])
            },
            containers_tree_unchanged(*old(self), *self),
            containers_owned_proc_unchanged(*old(self), *self),
            processes_unchanged(*old(self), *self),
            self.container_dom() == old(self).container_dom(),
            self.thread_dom() == old(self).thread_dom(),
            threads_unchanged_except(*old(self), *self, set![thread_ptr]),
            self.get_thread(thread_ptr).endpoint_descriptors@ 
                =~= old(self).get_thread(thread_ptr).endpoint_descriptors@.update(edp_idx as int, None),
            self.get_thread(thread_ptr).blocking_endpoint_index
                =~= old(self).get_thread(thread_ptr).blocking_endpoint_index,
            old(self).get_thread(thread_ptr).state == self.get_thread(thread_ptr).state,
            old(self).get_thread(thread_ptr).owning_proc == self.get_thread(thread_ptr).owning_proc,
    {

        let endpint_op = self.get_thread(thread_ptr).endpoint_descriptors.get(edp_idx);
        if endpint_op.is_none(){
            return None;
        }
        let endpoint_ptr = endpint_op.unwrap();
        let old_rf_counter = 
            self.get_endpoint(endpoint_ptr).rf_counter;
        let endpoint_owning_container = 
            self.get_endpoint(endpoint_ptr).owning_container;
        let mut thread_perm = Tracked(self.thread_perms.borrow_mut().tracked_remove(thread_ptr));
        thread_set_endpoint_descriptor(thread_ptr, &mut thread_perm, edp_idx, None);

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );

        endpoint_remove_ref(endpoint_ptr, &mut endpoint_perm, thread_ptr, edp_idx);

        if old_rf_counter == 1 {
            let ret = endpoint_to_page(endpoint_ptr, endpoint_perm);
            let mut container_perm = Tracked(self.container_perms.borrow_mut().tracked_remove(endpoint_owning_container));
            container_pop_endpoint(endpoint_owning_container, &mut container_perm, endpoint_ptr);
            return Some(ret);
        }

        None
    }
}

} // verus!
