module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Proper
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/-
Lemma 30.19.2

Let `S = Spec(A)`, where `A` is a Noetherian ring. Let `f : X ⟶ S` be a
proper morphism and let `F` be a coherent `O_X`-module. Then
`H^i(X, F)` is a finite `A`-module for every `i ≥ 0`.
-/
@[stacks 02O6] #check
  (AlgebraicGeometry.Scheme.Hom.cohomologyFinite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
      (F : X.Modules) [F.IsCoherent] (i : ℕ),
      Module.Finite A (AlgebraicGeometry.Scheme.Hom.cohomology f F i))
