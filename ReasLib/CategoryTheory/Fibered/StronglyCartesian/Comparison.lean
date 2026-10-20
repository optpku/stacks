module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-!
# Comparing strongly cartesian lifts

Mathlib's canonical comparison between strongly cartesian lifts is typeclass-driven. This leaf
provides the ordinary-argument boundary needed when cartesianness is available as local proof data,
without asking clients to install noncanonical instances.
-/

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory

namespace Functor.IsHomLift

variable {C : Type uC} {S : Type uS} [Category.{vC} C] [Category.{vS} S]
variable {p : S ⥤ C} {R T : C} {a b : S} {f : R ⟶ T} {φ : a ⟶ b}

/-- An explicitly certified lift which is an isomorphism is strongly cartesian.

This is the ordinary-argument boundary for mathlib's typeclass-driven
`IsStronglyCartesian.of_isIso` instance. It is useful for noncanonical or proof-indexed lifts
which should not be installed in the surrounding instance environment. -/
theorem isStronglyCartesian_of_isIso
    (hφ : p.IsHomLift f φ) [IsIso φ] :
    p.IsStronglyCartesian f φ :=
  @Functor.IsStronglyCartesian.of_isIso C S _ _ p R T a b f φ hφ inferInstance

end Functor.IsHomLift

namespace Functor.IsStronglyCartesian

variable {C : Type uC} {S : Type uS} [Category.{vC} C] [Category.{vS} S]
variable {p : S ⥤ C}

namespace DomainIso

/-- The canonical isomorphism between the domains of two explicitly certified strongly cartesian
arrows whose base domains are isomorphic.

Mathlib's `domainIsoOfBaseIso` presents the two certificates as instance arguments. This adapter
passes them directly, so using the construction does not modify the surrounding instance scope. -/
noncomputable def ofBaseIso (p : S ⥤ C)
    {R R' T : C} {a a' b : S} {f : R ⟶ T} {f' : R' ⟶ T} {g : R' ≅ R}
    (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    (hφ : p.IsStronglyCartesian f φ) (hφ' : p.IsStronglyCartesian f' φ') :
    a' ≅ a :=
  @domainIsoOfBaseIso _ _ _ _ p _ _ _ _ _ _ _ _ _ h φ φ' hφ hφ'

/-- The forward comparison lies over the forward base isomorphism. -/
theorem ofBaseIso.hom_isHomLift (p : S ⥤ C)
    {R R' T : C} {a a' b : S} {f : R ⟶ T} {f' : R' ⟶ T} {g : R' ≅ R}
    (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    (hφ : p.IsStronglyCartesian f φ) (hφ' : p.IsStronglyCartesian f' φ') :
    p.IsHomLift g.hom (ofBaseIso p h φ φ' hφ hφ').hom := sorry

/-- The inverse comparison lies over the inverse base isomorphism. -/
theorem ofBaseIso.inv_isHomLift (p : S ⥤ C)
    {R R' T : C} {a a' b : S} {f : R ⟶ T} {f' : R' ⟶ T} {g : R' ≅ R}
    (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    (hφ : p.IsStronglyCartesian f φ) (hφ' : p.IsStronglyCartesian f' φ') :
    p.IsHomLift g.inv (ofBaseIso p h φ φ' hφ hφ').inv := sorry

/-- The forward domain comparison identifies the first cartesian arrow with the second. -/
@[reassoc]
theorem ofBaseIso.hom_fac (p : S ⥤ C)
    {R R' T : C} {a a' b : S} {f : R ⟶ T} {f' : R' ⟶ T} {g : R' ≅ R}
    (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    (hφ : p.IsStronglyCartesian f φ) (hφ' : p.IsStronglyCartesian f' φ') :
    (ofBaseIso p h φ φ' hφ hφ').hom ≫ φ = φ' := sorry

/-- The inverse domain comparison identifies the second cartesian arrow with the first. -/
@[reassoc]
theorem ofBaseIso.inv_fac (p : S ⥤ C)
    {R R' T : C} {a a' b : S} {f : R ⟶ T} {f' : R' ⟶ T} {g : R' ≅ R}
    (h : f' = g.hom ≫ f) (φ : a ⟶ b) (φ' : a' ⟶ b)
    (hφ : p.IsStronglyCartesian f φ) (hφ' : p.IsStronglyCartesian f' φ') :
    (ofBaseIso p h φ φ' hφ hφ').inv ≫ φ' = φ := sorry

/- Data audit: `ofBaseIso` delegates to mathlib's canonical cartesian-lift comparison. Its
underlying maps are determined by the two strongly cartesian universal properties; the explicit
certificates contribute only proposition-valued lift and inverse-law fields. -/

end DomainIso

end Functor.IsStronglyCartesian

end CategoryTheory
