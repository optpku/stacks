module

public import stacks_project.Chap71.Definition_71_2_2_WeakAss
public import stacks_project.Chap71.Definition_71_2_2_Associated
import StacksCheckRecall

/-!
# Definition 71.2.2

Weakly associated points of quasi-coherent modules on algebraic spaces, the
locus `WeakAss(F)`, the space-level locus `WeakAss(X) = WeakAss(𝒪_X)`, and the
locally Noetherian identification `Ass = WeakAss`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.2.2 (1): a point `x ∈ |X|` is weakly associated to a
quasi-coherent `𝒪_X`-module `F` when the equivalent étale-chart and étale-stalk
conditions of Lemma 71.2.1 hold. -/
@[stacks 0CTX] #check
  (@Modules.weaklyAssociatedAt :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → X.Modules → Points X → Prop)

/- Definition 71.2.2 (2): `WeakAss(F)` is the set of weakly associated points of
`F`. -/
@[stacks 0CTX] #check
  (@Modules.weakAss :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → X.Modules → Set (Points X))

/- Definition 71.2.2 (3): the weakly associated points of `X` are the weakly
associated points of `𝒪_X`. -/
@[stacks 0CTX] #check
  (@weakAss : {S : Scheme.{u}} → (X : AlgebraicSpace S) → Set (Points X))

/- Definition 71.2.2 (4): if `X` is locally Noetherian, then `x` is associated to
`F` if and only if it is weakly associated, and `Ass(F) = WeakAss(F)`. -/
@[stacks 0CTX] #check
  (@Modules.associatedPoints :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → [IsLocallyNoetherian X] →
      X.Modules → Set (Points X))

/- Definition 71.2.2 (5): if `X` is locally Noetherian, then `x` is an associated
point of `X` if and only if it is a weakly associated point of `X`. -/
@[stacks 0CTX] #check
  (@associatedPoints :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) → [IsLocallyNoetherian X] →
      Set (Points X))

#check
  (@Modules.mem_weakAss_iff :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → (F : X.Modules) → (x : Points X) →
      (x ∈ F.weakAss ↔ F.weaklyAssociatedAt x))
#check
  (@Modules.associatedPoints_eq_weakAss :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} → [IsLocallyNoetherian X] →
      (F : X.Modules) → Modules.associatedPoints F = F.weakAss)
