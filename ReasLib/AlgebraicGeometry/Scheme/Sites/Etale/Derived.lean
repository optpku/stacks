/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Abelian
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Derived

variable {A B C : Scheme.{u}}

/-- The unbounded derived inverse image on abelian sheaves on small étale sites. -/
noncomputable abbrev inverseImage (a : A ⟶ B) :
    DerivedCategory (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.KInjective.left (Abelian.inverseImageExact a)

/-- The unbounded total right-derived direct image on small étale sites. -/
noncomputable abbrev directImage (a : A ⟶ B) :
    DerivedCategory (Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Adjunction.Derived.KInjective.right (Abelian.directImage a)

/-- The unbounded derived inverse image is left adjoint to the total derived direct image. -/
noncomputable def adjunction (a : A ⟶ B) : inverseImage a ⊣ directImage a :=
  Adjunction.Derived.KInjective.adjunction (Abelian.inverseImageExact a)
    (Abelian.directImage a) (Abelian.adjunction a)

/-- Composition of derived inverse images is canonically identified with the derived inverse image
of the composite. -/
noncomputable def inverseImageCompIso (a : A ⟶ B) (b : B ⟶ C) :
    inverseImage (a ≫ b) ≅ inverseImage b ⋙ inverseImage a :=
  let e : (Abelian.inverseImageExact b).comp (Abelian.inverseImageExact a) ≅
      Abelian.inverseImageExact (a ≫ b) :=
    ObjectProperty.isoMk (exactFunctor _ _) (Abelian.inverseImageCompIso a b).symm
  (ExactFunctor.MapDerivedCategory.mapIso e).symm ≪≫
    ExactFunctor.MapDerivedCategory.compFunctorIso
      (Abelian.inverseImageExact b) (Abelian.inverseImageExact a)

/-- The degree-`q` higher direct image of a sheaf on a small étale site. -/
noncomputable abbrev higherDirectImage (a : A ⟶ B) (q : ℕ) :
    Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  DerivedCategory.singleFunctor
      (Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
    directImage a ⋙
    DerivedCategory.homologyFunctor
      (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)

end AlgebraicGeometry.Scheme.Etale.Derived

end
