/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertibleQuotient.Pullback

/-! Actual E-dependent quotient functor, before constructing its small representing atlas.
No projective bundle, tautological line, or higher Chern family is selected here.
-/
@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.MonoidalCategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveQuotientFunctor
variable {S : Scheme.{u}} {X : AlgebraicSpace S} (E : X.Modules)

/-- A projective point over g is an actual epimorphic invertible quotient of g*E. -/
abbrev Point (T : Over X) :=
  CategoryTheory.InvertibleQuotient.IsoClass ((Modules.pullback T.hom).obj E)

/-- The canonical source comparison along a morphism of X-spaces. -/
def sourceIso {T U : Over X} (a : U ⟶ T) :
    (Modules.pullback a.left).obj ((Modules.pullback T.hom).obj E) ≅
      (Modules.pullback U.hom).obj E :=
  (Modules.pullbackCompIso a.left T.hom).app E ≪≫
    eqToIso (congrArg (fun h ↦ (Modules.pullback h).obj E) a.w)

/-- Pullback of the quotient itself, followed by its forced source comparison. -/
def restrictRepresentative {T U : Over X} (a : U ⟶ T)
    (q : CategoryTheory.InvertibleQuotient ((Modules.pullback T.hom).obj E)) :
    CategoryTheory.InvertibleQuotient ((Modules.pullback U.hom).obj E) :=
  CategoryTheory.InvertibleQuotient.precomposeIso (sourceIso E a).symm
    (AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient.pullback a.left q)

theorem restrictRepresentative_rel {T U : Over X} (a : U ⟶ T)
    {q q' : CategoryTheory.InvertibleQuotient ((Modules.pullback T.hom).obj E)}
    (h : CategoryTheory.InvertibleQuotient.Rel q q') :
    CategoryTheory.InvertibleQuotient.Rel
      (restrictRepresentative E a q) (restrictRepresentative E a q') :=
  CategoryTheory.InvertibleQuotient.precomposeIso_rel (sourceIso E a).symm
    (AlgebraicGeometry.AlgebraicSpace.InvertibleQuotient.pullback_rel a.left h)

def restrict {T U : Over X} (a : U ⟶ T) : Point E T → Point E U :=
  Quotient.map (restrictRepresentative E a) (fun _ _ ↦ restrictRepresentative_rel E a)

@[simp] theorem restrict_mk {T U : Over X} (a : U ⟶ T)
    (q : CategoryTheory.InvertibleQuotient ((Modules.pullback T.hom).obj E)) :
    restrict E a (CategoryTheory.InvertibleQuotient.IsoClass.mk q) =
      CategoryTheory.InvertibleQuotient.IsoClass.mk (restrictRepresentative E a q) := rfl

/-- Unit law of the specified pullback quotient-class map. -/
theorem restrict_id (T : Over X) : restrict E (𝟙 T) = id := by
  sorry

/-- Associativity of the specified pullback quotient-class map. -/
theorem restrict_comp {T U V : Over X} (a : V ⟶ U) (b : U ⟶ T) :
    restrict E (a ≫ b) = restrict E a ∘ restrict E b := by
  sorry

/-- The projective quotient presheaf on X-spaces. Its values retain the honest
large universe; a small scheme-test presentation is still a separate task. -/
def functor : (Over X)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Point E T.unop
  map a := TypeCat.ofHom (restrict E a.unop)
  map_id T := by
    ext q
    exact congrFun (restrict_id E T.unop) q
  map_comp a b := by
    ext q
    exact congrFun (restrict_comp E b.unop a.unop) q

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveQuotientFunctor
