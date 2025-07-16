# ProtocolB

We first model the basic components; block, chain, vaidator, and system. A block (`Block`) is represented as a string (e.g. its hash). A chain (`CHain`) is a list of Blocks. A validator (`Validator`) is modeled by its current chain and a flag indicating if it has crashed. A system of this protocol B (`SystemB`) consists of a list of validators and a designated leader.

```haskell
abbrev Block := String

abbrev Chain := List Block

structure ValidatorB where
    chain   : List Block
    crashed : Bool
    id      : ℕ
deriving Repr

structure SystemB  where
  validators : List ValidatorB
  leader     : ℕ
deriving Repr
```

We then defin the consistency of the system, which is the goal of our proving. Recall that two chains are consistent if one is a prefix of the other. This ensures there are no forks among the chains.

```
def ChainsAreConsistent (c₁ c₂ : Chain) : Prop :=
  c₁ <+: c₂ ∨ c₂ <+: c₁
```
