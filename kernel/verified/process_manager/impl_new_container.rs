use vstd::prelude::*;
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
use crate::quota::Quota;

impl ProcessManager {
    pub fn new_container_with_endpoint(
        &mut self,
        thread_ptr: ThreadPtr,
        endpoint_index: EndpointIdx,
        pt_regs: Registers,
        new_pcid: Pcid,
        new_quota: &Quota,
        page_ptr_1: PagePtr,
        page_perm_1: Tracked<PagePerm4k>,
        page_ptr_2: PagePtr,
        page_perm_2: Tracked<PagePerm4k>,
        page_ptr_3: PagePtr,
        page_perm_3: Tracked<PagePerm4k>,
    )
        requires
            old(self).wf(),
            old(self).thread_dom().contains(thread_ptr),
            old(self).page_closure().contains(page_ptr_1) == false,
            old(self).page_closure().contains(page_ptr_2) == false,
            old(self).page_closure().contains(page_ptr_3) == false,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).depth != usize::MAX,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_4k - 3 >= new_quota.mem_4k,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.spec_greater(new_quota),
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).children.len() < CONTAINER_CHILD_LIST_LEN,
            0 <= endpoint_index < MAX_NUM_ENDPOINT_DESCRIPTORS,
            old(self).get_endpoint_by_endpoint_idx(thread_ptr, endpoint_index).is_Some() || old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).is_Some(),
            old(self).get_endpoint_by_endpoint_idx(thread_ptr,endpoint_index).unwrap().rf_counter_is_full() == false 
            || old(self).get_endpoint(old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),).rf_counter_is_full() == false,
            forall|p_ptr_i: ProcPtr|
                #![trigger old(self).proc_dom().contains(p_ptr_i) ]
                old(self).proc_dom().contains(p_ptr_i) ==> old(self).get_proc(p_ptr_i).pcid != new_pcid,
            page_perm_1@.is_init(),
            page_perm_1@.addr() == page_ptr_1,
            page_perm_2@.is_init(),
            page_perm_2@.addr() == page_ptr_2,
            page_perm_3@.is_init(),
            page_perm_3@.addr() == page_ptr_3,
            page_ptr_1 != page_ptr_2,
            page_ptr_1 != page_ptr_3,
            page_ptr_2 != page_ptr_3,
        ensures
            self.wf(),
            self.page_closure() =~= old(self).page_closure().insert(page_ptr_1).insert(
                page_ptr_2,
            ).insert(page_ptr_3),
            self.proc_dom() =~= old(self).proc_dom().insert(page_ptr_2),
            self.endpoint_dom() == old(self).endpoint_dom(),
            self.container_dom() == old(self).container_dom().insert(page_ptr_1),
            self.thread_dom() == old(self).thread_dom().insert(page_ptr_3),
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_4k
                - 3 - new_quota.mem_4k == self.get_container(
                self.get_thread(thread_ptr).owning_container,
            ).quota.mem_4k,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_2m
                - new_quota.mem_2m == self.get_container(
                self.get_thread(thread_ptr).owning_container,
            ).quota.mem_2m,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_1g
                - new_quota.mem_1g == self.get_container(
                self.get_thread(thread_ptr).owning_container,
            ).quota.mem_1g,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.pcid
                - new_quota.pcid == self.get_container(
                self.get_thread(thread_ptr).owning_container,
            ).quota.pcid,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.ioid
                - new_quota.ioid == self.get_container(
                self.get_thread(thread_ptr).owning_container,
            ).quota.ioid,
            forall|p_ptr: ProcPtr|
                #![trigger self.get_proc(p_ptr)]
                old(self).proc_dom().contains(p_ptr) ==> self.get_proc(p_ptr) =~= old(
                    self,
                ).get_proc(p_ptr),
            forall|c_ptr: ContainerPtr|
                #![trigger self.get_container(c_ptr)]
                old(self).container_dom().contains(c_ptr) && c_ptr != old(self).get_thread(
                    thread_ptr,
                ).owning_container ==> self.get_container(c_ptr).owned_procs =~= old(
                    self,
                ).get_container(c_ptr).owned_procs && self.get_container(c_ptr).parent =~= old(
                    self,
                ).get_container(c_ptr).parent && self.get_container(c_ptr).parent_rev_ptr =~= old(
                    self,
                ).get_container(c_ptr).parent_rev_ptr && self.get_container(c_ptr).children =~= old(
                    self,
                ).get_container(c_ptr).children && self.get_container(c_ptr).owned_endpoints
                    =~= old(self).get_container(c_ptr).owned_endpoints && self.get_container(
                    c_ptr,
                ).quota =~= old(self).get_container(c_ptr).quota
                // &&
                // self.get_container(c_ptr).mem_used =~= old(self).get_container(c_ptr).mem_used
                 && self.get_container(c_ptr).owned_cpus =~= old(self).get_container(
                    c_ptr,
                ).owned_cpus && self.get_container(c_ptr).scheduler =~= old(self).get_container(
                    c_ptr,
                ).scheduler && self.get_container(c_ptr).owned_threads =~= old(self).get_container(
                    c_ptr,
                ).owned_threads && self.get_container(c_ptr).depth =~= old(self).get_container(
                    c_ptr,
                ).depth && self.get_container(c_ptr).uppertree_seq =~= old(self).get_container(
                    c_ptr,
                ).uppertree_seq,
            forall|c_ptr: ContainerPtr|
                #![trigger self.get_container(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    page_ptr_1,
                ).uppertree_seq@.contains(c_ptr) ==> self.get_container(c_ptr).subtree_set@
                    =~= self.get_container(c_ptr).subtree_set@.insert(page_ptr_1),
            forall|c_ptr: ContainerPtr|
                #![trigger self.get_container(c_ptr)]
                self.container_dom().contains(c_ptr) && self.get_container(
                    page_ptr_1,
                ).uppertree_seq@.contains(c_ptr) == false ==> self.get_container(c_ptr).subtree_set
                    =~= self.get_container(c_ptr).subtree_set,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_procs
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_procs,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).parent =~= old(
                self,
            ).get_container(old(self).get_thread(thread_ptr).owning_container).parent,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).children@ =~= old(
                self,
            ).get_container(old(self).get_thread(thread_ptr).owning_container).children@.push(
                page_ptr_1,
            ),
            self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_endpoints
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_endpoints,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_4k
                - 3 - new_quota.mem_4k == self.get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.mem_4k,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_2m
                - new_quota.mem_2m == self.get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.mem_2m,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.mem_1g
                - new_quota.mem_1g == self.get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.mem_1g,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.pcid
                - new_quota.pcid == self.get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.pcid,
            old(self).get_container(old(self).get_thread(thread_ptr).owning_container).quota.ioid
                - new_quota.ioid == self.get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).quota.ioid,
            // self.get_container(old(self).get_thread(thread_ptr).owning_container).mem_used =~= old(self).get_container(old(self).get_thread(thread_ptr).owning_container).mem_used,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_cpus
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_cpus,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).scheduler =~= old(
                self,
            ).get_container(old(self).get_thread(thread_ptr).owning_container).scheduler,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).owned_threads
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).owned_threads,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).depth =~= old(
                self,
            ).get_container(old(self).get_thread(thread_ptr).owning_container).depth,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).uppertree_seq
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).uppertree_seq,
            self.get_container(old(self).get_thread(thread_ptr).owning_container).subtree_set@
                =~= old(self).get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).subtree_set@.insert(page_ptr_1),
            self.get_container(page_ptr_1).owned_procs@ =~= Seq::<ProcPtr>::empty().push(
                page_ptr_2,
            ),
            self.get_container(page_ptr_1).parent =~= Some(
                old(self).get_thread(thread_ptr).owning_container,
            ),
            self.get_container(page_ptr_1).children@ =~= Seq::<ContainerPtr>::empty(),
            self.get_container(page_ptr_1).owned_endpoints@ =~= Set::<EndpointPtr>::empty(),
            self.get_container(page_ptr_1).quota =~= *new_quota,
            // self.get_container(page_ptr_1).mem_used =~= 0,
            self.get_container(page_ptr_1).owned_cpus.wf(),
            self.get_container(page_ptr_1).owned_cpus@ =~= Set::<CpuId>::empty(),
            self.get_container(page_ptr_1).scheduler.wf(),
            self.get_container(page_ptr_1).scheduler@ =~= Seq::<ThreadPtr>::empty().push(
                page_ptr_3,
            ),
            self.get_container(page_ptr_1).owned_threads@.finite(),
            self.get_container(page_ptr_1).owned_threads@ =~= Set::<ThreadPtr>::empty().insert(
                page_ptr_3,
            ),
            self.get_container(page_ptr_1).depth as int =~= self.get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).depth + 1,
            self.get_container(page_ptr_1).uppertree_seq@ =~= self.get_container(
                old(self).get_thread(thread_ptr).owning_container,
            ).uppertree_seq@.push(old(self).get_thread(thread_ptr).owning_container),
            self.get_container(page_ptr_1).subtree_set@ =~= Set::<ContainerPtr>::empty(),
            forall|t_ptr: ThreadPtr|
                #![trigger old(self).get_thread(t_ptr)]
                old(self).thread_dom().contains(t_ptr) ==> old(self).get_thread(t_ptr)
                    =~= self.get_thread(t_ptr),
            forall|e_ptr: EndpointPtr|
                #![trigger self.get_endpoint(e_ptr)]
                self.endpoint_dom().contains(e_ptr) && e_ptr != old(
                    self,
                ).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap() ==> old(
                    self,
                ).get_endpoint(e_ptr) =~= self.get_endpoint(e_ptr),
            self.get_container(page_ptr_1).children@ == Seq::<ContainerPtr>::empty(),
            self.get_container(page_ptr_1).owned_procs@ == Seq::<ProcPtr>::empty().push(page_ptr_2),
            self.get_container(page_ptr_1).owned_threads@ == Set::<ThreadPtr>::empty().insert(
                page_ptr_3,
            ),
            self.get_container(page_ptr_1).quota == new_quota,
            self.get_proc(page_ptr_2).pcid =~= new_pcid,
            self.get_proc(page_ptr_2).ioid.is_None(),
            self.get_proc(page_ptr_2).owned_threads@ == Seq::<ThreadPtr>::empty().push(page_ptr_3),
            self.get_proc(page_ptr_2).owning_container == page_ptr_1,
            self.get_thread(page_ptr_3).owning_container == page_ptr_1,
            self.get_thread(page_ptr_3).endpoint_descriptors@ =~= Seq::new(
                MAX_NUM_ENDPOINT_DESCRIPTORS as nat,
                |i: int| { None },
            ).update(
                0,
                Some(
                    old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
                ),
            ),
            self.get_container(self.get_thread(thread_ptr).owning_container).children@ =~= old(
                self,
            ).get_container(self.get_thread(thread_ptr).owning_container).children@.push(
                page_ptr_1,
            ),
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_procs@ =~= old(
                self,
            ).get_container(self.get_thread(thread_ptr).owning_container).owned_procs@,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_endpoints@
                =~= old(self).get_container(
                self.get_thread(thread_ptr).owning_container,
            ).owned_endpoints@,
            self.get_container(self.get_thread(thread_ptr).owning_container).owned_threads@ =~= old(
                self,
            ).get_container(self.get_thread(thread_ptr).owning_container).owned_threads@,
            self.get_endpoint(
                old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
            ).owning_threads@ =~= old(self).get_endpoint(
                old(self).get_endpoint_ptr_by_endpoint_idx(thread_ptr, endpoint_index).unwrap(),
            ).owning_threads@.insert((page_ptr_3, 0)),
    {
    
        let old_container_ptr = self.get_thread(thread_ptr).owning_container;
        let mut old_quota = self.get_container(old_container_ptr).quota;
        let endpoint_ptr = self.get_thread(thread_ptr).endpoint_descriptors.get(
            endpoint_index,
        ).unwrap();
        let new_upper_tree_ghost = Ghost(
            self.get_container(old_container_ptr).uppertree_seq@.push(old_container_ptr),
        );
        let old_depth = self.get_container(old_container_ptr).depth;

        old_quota.subtract_mem_4k(3);
        old_quota.subtract_new_quota(new_quota);
        let mut old_container_perm = Tracked(
            self.container_perms.borrow_mut().tracked_remove(old_container_ptr),
        );
        container_set_quota(old_container_ptr, &mut old_container_perm, &old_quota);
        let child_list_node_ref = container_push_child(
            old_container_ptr,
            &mut old_container_perm,
            page_ptr_1,
        );

        let (new_container_ptr, mut new_container_perm) = page_to_container_tree_version_1(
            page_ptr_1,
            page_perm_1,
            old_container_ptr,
            child_list_node_ref,
            *new_quota,
            ArraySet::<NUM_CPUS>::new(),
            old_depth + 1,
            Ghost(Set::<ContainerPtr>::empty()),
            new_upper_tree_ghost,
            Some(page_ptr_2),
        );

        let proc_list_node_ref = container_push_proc(
            new_container_ptr,
            &mut new_container_perm,
            page_ptr_2,
        );
        let scheduler_node_ref = scheduler_push_thread(
            new_container_ptr,
            &mut new_container_perm,
            &page_ptr_3,
        );
        container_set_owned_threads(
            new_container_ptr,
            &mut new_container_perm,
            Ghost(Set::<ThreadPtr>::empty().insert(page_ptr_3)),
        );

        container_perms_update_subtree_set(
            &mut self.container_perms,
            new_upper_tree_ghost,
            new_container_ptr,
        );

        let (new_proc_ptr, mut proc_perm, proc_thread_list_node_ref) =
            page_to_proc_with_first_thread(
            page_ptr_2,
            page_perm_2,
            new_container_ptr,
            proc_list_node_ref,
            new_pcid,
            None,
            page_ptr_3,
            None,
            None,
            Ghost(Seq::empty()),
            Ghost(Set::empty()),
            0,
        );
        let (new_thread_ptr, thread_perm) = page_to_thread_with_endpoint(
            page_ptr_3,
            page_perm_3,
            &pt_regs,
            new_container_ptr,
            new_proc_ptr,
            proc_thread_list_node_ref,
            scheduler_node_ref,
            endpoint_ptr,
        );

        let mut endpoint_perm = Tracked(
            self.endpoint_perms.borrow_mut().tracked_remove(endpoint_ptr),
        );
        endpoint_add_ref(endpoint_ptr, &mut endpoint_perm, new_thread_ptr, 0);

    }
}

} // verus!
