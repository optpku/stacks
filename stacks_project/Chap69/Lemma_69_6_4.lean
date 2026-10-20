module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AlternatingCech.OffDiagonal

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

/- Lemma 69.6.4. The symmetric group acts freely on the off-diagonal fibre product,
and Hom from the exterior power of extension by zero identifies naturally with
sign-anti-invariant sections. -/
@[stacks 0726] #check (AlgebraicGeometry.AlgebraicSpace.homKoszul_antiInvariants :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] [Separated f] (p : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
    (preadditiveYoneda.obj F).obj (op ((koszulComplex f).X p)) ≅
      IntegerCharacter.invariants (offDiagonalSectionsAction f (p + 1) F)
        (IntegerCharacter.permutationSign (p + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.instIsFree_offDiagonalPerm :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] [Separated f] (p : ℕ),
    IsFree (offDiagonalPermLift f (p + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.homKoszul_antiInvariants_natural :
  ∀ {S : Scheme.{u}} {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Surjective f] [Separated f] (p : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G),
    (preadditiveYoneda.map φ).app (op ((koszulComplex f).X p)) ≫
        (homKoszul_antiInvariants f p G).hom =
      (homKoszul_antiInvariants f p F).hom ≫ offDiagonalAntiInvariantsMap f (p + 1) φ)
