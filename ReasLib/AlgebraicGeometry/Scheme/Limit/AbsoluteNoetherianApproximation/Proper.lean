module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.AbsoluteNoetherianApproximation
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Limit.Proper

/-!
# Proper absolute Noetherian approximation

This file records inverse-system approximations of proper morphisms by proper morphisms whose
bases are of finite type over `ℤ`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- Fixed source and base inverse systems form a proper absolute Noetherian approximation of
`f : X ⟶ S` when their cones with vertices `X` and `S` are limiting, their component maps
recover `f`, all source and base transitions are affine, all component maps are proper, and all
bases are of finite type over `ℤ`. -/
def IsProperAbsoluteNoetherianApproximation {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (Xsys : OrderDual I ⥤ Scheme.{u})
    (Ssys : OrderDual I ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (πX : (Functor.const (OrderDual I)).obj X ⟶ Xsys)
    (πS : (Functor.const (OrderDual I)).obj S ⟶
      Ssys ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (φ : Xsys ⟶ Ssys ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))) : Prop :=
  Nonempty (IsLimit (⟨X, πX⟩ : Cone Xsys)) ∧
    Nonempty (IsLimit (⟨S, πS⟩ :
      Cone (Ssys ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))))) ∧
    (∀ i : I, πX.app i ≫ φ.app i = f ≫ πS.app i) ∧
    (∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (Xsys.map (homOfLE hii'))) ∧
    (∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (Ssys.map (homOfLE hii')).left) ∧
    (∀ i : I, IsProper (φ.app i)) ∧
    ∀ i : I, Scheme.Hom.FiniteType (Ssys.obj i).hom

/-- A fixed pair of inverse systems is a proper absolute Noetherian approximation exactly when
its source and base cones are limiting, its components recover the original morphism, its
transitions are affine, its components are proper, and its bases are of finite type over `ℤ`. -/
theorem isProperAbsoluteNoetherianApproximation_iff {I : Type u} [Preorder I]
    {X S : Scheme.{u}} (f : X ⟶ S) (Xsys : OrderDual I ⥤ Scheme.{u})
    (Ssys : OrderDual I ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (πX : (Functor.const (OrderDual I)).obj X ⟶ Xsys)
    (πS : (Functor.const (OrderDual I)).obj S ⟶
      Ssys ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (φ : Xsys ⟶ Ssys ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    IsProperAbsoluteNoetherianApproximation f Xsys Ssys πX πS φ ↔
      Nonempty (IsLimit (⟨X, πX⟩ : Cone Xsys)) ∧
        Nonempty (IsLimit (⟨S, πS⟩ :
          Cone (Ssys ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))))) ∧
        (∀ i : I, πX.app i ≫ φ.app i = f ≫ πS.app i) ∧
        (∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (Xsys.map (homOfLE hii'))) ∧
        (∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (Ssys.map (homOfLE hii')).left) ∧
        (∀ i : I, IsProper (φ.app i)) ∧
        ∀ i : I, Scheme.Hom.FiniteType (Ssys.obj i).hom := sorry

/-- Every proper morphism to a quasi-compact, quasi-separated scheme is the limit of a
nonempty directed inverse system of proper morphisms with affine source and base transitions
and bases of finite type over `ℤ`. -/
theorem exists_properAbsoluteNoetherianApproximation
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
      ∃ (_ : IsDirected I (· ≤ ·)), ∃ (Xsys : OrderDual I ⥤ Scheme.{u}),
        ∃ (Ssys : OrderDual I ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ)))),
          ∃ (πX : (Functor.const (OrderDual I)).obj X ⟶ Xsys),
            ∃ (πS : (Functor.const (OrderDual I)).obj S ⟶
              Ssys ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))),
              ∃ (φ : Xsys ⟶
                Ssys ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))),
                IsProperAbsoluteNoetherianApproximation f Xsys Ssys πX πS φ := sorry

end AlgebraicGeometry.Scheme.Limit
