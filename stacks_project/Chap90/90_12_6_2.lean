module

public import stacks_project.Chap90.«90_12_6_2_Action»
import StacksCheckRecall

/-!
# Action of derivations on the tangent space

A derivation `D : Derivation Λ k k` acts on the tangent space of a predeformation category by
cofibered pushforward along the dual-number automorphism `f_{1,D}`.
-/

@[expose] public section

open CategoryTheory

/- 90.12.6.2: the action `a : Derivation Λ k k × T F ⟶ T F` of a `Λ`-derivation of `k` on the
tangent space of a predeformation category, given by `a(D, [x]) = [f_{1,D,*}(x)]`, where
`f_{1,D}` is the automorphism `ArtinianLocalAlgCat.dualNumberAut D` of
`ArtinianLocalAlgCat.dualNumber Λ k` sending `inl r + inr v` to `inl r + inr (v + D r)`. -/
@[stacks 06SW]
#check Functor.derivationAction
