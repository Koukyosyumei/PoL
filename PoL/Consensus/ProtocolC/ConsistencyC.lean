import PoL.Consensus.ProtocolC.StateC

def protocolC_step
  (state : StateC) (new_block : Block) (current_view : ℕ) (next_leader: StateC → ℕ) : StateC :=
  let n := state.validators.length

  -- Phase 1: Collect known chains with views from non-crashed validators
  let known_chains_with_views := state.validators.filterMap (λ v =>
    if ¬v.crashed then some v.known_chain else none)

  -- Phase 2: Leader proposes if read quorum achieved
  let proposal :=
    if has_read_quorum known_chains_with_views n then
      let base_chain := get_most_recent_chain known_chains_with_views
      let new_chain_with_view : ChainWithView :=
        { chain := base_chain ++ [new_block], view := current_view }
      some new_chain_with_view
    else none

  -- Phase 3: Update validators based on quorum conditions
  let updated_validators := state.validators.map (λ v =>
    if ¬v.crashed then
      match proposal with
      | some new_chain_with_view =>
        let ack_count := known_chains_with_views.length
        if has_write_quorum ack_count n then
          { finalized_chain := new_chain_with_view.chain,
            known_chain := new_chain_with_view,
            crashed := v.crashed,
            id := v.id }
        else
          { finalized_chain := v.finalized_chain,
            known_chain := new_chain_with_view,
            crashed := v.crashed,
            id := v.id }
      | none => v
    else v)

  { validators := updated_validators,
    leader := next_leader state }
