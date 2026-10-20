module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.ProperBirational
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 53.18.4 (1): If `X` is proper over a field `k` and has dimension at most one,
then a proper birational morphism `f : X' ⟶ X` satisfies the stated structure-sheaf
cohomology inequality. -/
@[stacks 0CE4] #check
  (AlgebraicGeometry.Scheme.Hom.ProperBirational.structureSheafH1Finrank_le :
    ∀ {k : Type u} [Field k] {X X' : Scheme.{u}}
      (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
      (f : X' ⟶ X) [IsBirational f] [IsProper f]
      (hdim : topologicalKrullDim X ≤ 1),
      Scheme.Hom.cohomologyFinrank (f ≫ p)
          (SheafOfModules.unit X'.ringCatSheaf : X'.Modules) 1 ≤
        Scheme.Hom.cohomologyFinrank p
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1)

/- Lemma 53.18.4 (2): Under the hypotheses of (1), if `X` is reduced, the map
on global functions induced by `f` is surjective, and equality holds, then `f`
is an isomorphism. -/
@[stacks 0CE4] #check
  (AlgebraicGeometry.Scheme.Hom.ProperBirational.isIso_of_structureSheafH1Finrank_eq :
    ∀ {k : Type u} [Field k] {X X' : Scheme.{u}}
      (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
      (f : X' ⟶ X) [IsBirational f] [IsProper f] [IsReduced X]
      (hdim : topologicalKrullDim X ≤ 1)
      (hΓ : Function.Surjective f.appTop)
      (hH1 : Scheme.Hom.cohomologyFinrank (f ≫ p)
          (SheafOfModules.unit X'.ringCatSheaf : X'.Modules) 1 =
        Scheme.Hom.cohomologyFinrank p
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) 1),
      IsIso f)
