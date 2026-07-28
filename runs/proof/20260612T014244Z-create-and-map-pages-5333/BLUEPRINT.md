# create_and_map_pages frontier 5333

- target: alloc_and_map / alloc_and_map_io / range_alloc_and_map / range_alloc_and_map_io
- baseline: prior report says kernel::create_and_map_pages 6 verified, 6 errors; full OS 363 verified, 117 errors
- result: no source edit
  - focused alloc_and_map: 1 verified, 0 errors
  - focused alloc_and_map_io: 1 verified, 0 errors
  - focused range_alloc_and_map: 2 verified, 0 errors
  - focused range_alloc_and_map_io: 2 verified, 0 errors
  - module kernel::create_and_map_pages: 12 verified, 0 errors
  - full OS: 515 verified, 0 errors
  - shortcut scan in create_and_map_pages.rs: no assume/admit/proof_from_false/arbitrary/external_body/unimplemented matches
  - source diff for create_and_map_pages.rs: empty
- next: no create_and_map_pages frontier remains under the current checker contracts in this worktree; note that range_alloc_and_map_io still has mostly commented substantive postconditions
