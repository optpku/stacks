/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Representability of global sections

The functor of global functions is represented by the integral affine line.
The concrete equivalence and universal coordinate are exposed independently
of the naturality proof used to bundle the representing isomorphism.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GlobalSections

/-- Example 26.15.2 (1): the contravariant Type-valued functor of global
sections of schemes. -/
@[stacks 01JH]
def functor : Scheme.{u}ᵒᵖ ⥤ Type u :=
  Scheme.Γ ⋙ CategoryTheory.forget CommRingCat

/-- Example 26.15.2 (2): the integral affine line used as the representing
scheme for global sections. -/
@[stacks 01JH]
abbrev affineLine : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of (ULift.{u} ℤ)))

/-- Morphisms to the integral affine line are equivalent to global
sections. -/
@[stacks 01JH]
noncomputable def homEquiv (T : Scheme.{u}) :
    (T ⟶ affineLine) ≃ Γ(T, ⊤) :=
  ((Iso.refl T).homCongr
      (AffineSpace.SpecIso (ULift.{u} (Fin 1))
        (CommRingCat.of (ULift.{u} ℤ)))).trans <|
    (AffineSpace.toSpecMvPolyIntEquiv (ULift.{u} (Fin 1))).trans
      (Equiv.funUnique (ULift.{u} (Fin 1)) _)

/-- The objectwise isomorphism underlying representability of global
sections. -/
@[stacks 01JH "objectwise global-sections representation"]
noncomputable def componentIso (T : Scheme.{u}ᵒᵖ) :
    (yoneda.obj affineLine).obj T ≅ functor.obj T :=
  (homEquiv (unop T)).toIso

/-- Naturality of the morphism-to-global-sections equivalence. -/
@[stacks 01JH "naturality of global-sections representation"]
theorem componentIso_naturality {T T' : Scheme.{u}ᵒᵖ} (f : T ⟶ T') :
    (yoneda.obj affineLine).map f ≫ (componentIso T').hom =
      (componentIso T).hom ≫ functor.map f := sorry

/-- Example 26.15.2 (2): the natural isomorphism representing global
sections by the integral affine line. -/
@[stacks 01JH]
noncomputable def representingIso :
    yoneda.obj (affineLine : Scheme.{u}) ≅ functor :=
  NatIso.ofComponents componentIso (fun f ↦ componentIso_naturality f)

/-- The global-sections functor is representable. -/
@[stacks 01JH, instance]
noncomputable instance functor_isRepresentable : functor.IsRepresentable :=
  Functor.IsRepresentable.mk' representingIso

/-- Example 26.15.2 (3): the universal global section is the unique affine
coordinate. -/
@[stacks 01JH]
noncomputable def universalSection : Γ((affineLine : Scheme.{u}), ⊤) :=
  AffineSpace.coord (Spec (CommRingCat.of (ULift.{u} ℤ)))
    (ULift.up (0 : Fin 1))

/-- The representing equivalence sends a morphism to the pullback of the
universal section. -/
@[stacks 01JH]
theorem homEquiv_apply (T : Scheme.{u}) (f : T ⟶ affineLine) :
    homEquiv T f = Scheme.Γ.map f.op universalSection := sorry

/-- Example 26.15.2 (4): under affine global sections, the universal section
is the polynomial coordinate `X`. -/
@[stacks 01JH]
theorem universalSection_eq_coordinate :
    (AffineSpace.SpecIso (ULift.{u} (Fin 1))
      (CommRingCat.of (ULift.{u} ℤ))).inv.appTop universalSection =
    (Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) (ULift.{u} ℤ)))).inv
        (MvPolynomial.X (ULift.up (0 : Fin 1))) := sorry

end AlgebraicGeometry.Scheme.GlobalSections
