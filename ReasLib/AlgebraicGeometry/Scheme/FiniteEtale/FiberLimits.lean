module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Fiber
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Limits.FintypeCat

/-!
# Finite limits of geometric finite étale fibres

The set-valued fibre is the finite étale slice inclusion followed by the
representable functor of the geometric point. Native slice limit creation and
representable limit preservation supply the actual limiting lifts; the fully
faithful finite-set inclusion reflects them to the finite-valued fibre.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {X : Scheme.{u}}
variable {K : Type u} [Field K] [IsAlgClosed K]

/-- Geometric fibres over any scheme preserve finite limits through the
native finite étale slice inclusion and the representable point functor. -/
instance finiteFiber_preservesFiniteLimits (point : Spec (.of K) ⟶ X) :
    PreservesFiniteLimits (finiteFiber point) := by
  letI : MorphismProperty.HasOfPostcompProperty
      finiteEtaleMorphism finiteEtaleMorphism :=
    { of_postcomp := by
        intro Y Z W f g hg hfg
        letI : IsFinite g := hg.1
        letI : IsFinite (f ≫ g) := hfg.1
        exact ⟨IsFinite.of_comp f g,
          MorphismProperty.of_postcomp (W := @Etale) f g hg.2 hfg.2⟩ }
  letI : PreservesFiniteLimits (finiteFiber point ⋙ FintypeCat.incl) := by
    change PreservesFiniteLimits
      (MorphismProperty.Over.forget finiteEtaleMorphism ⊤ X ⋙
        coyoneda.obj (Opposite.op (Over.mk point)))
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves
    (finiteFiber point) FintypeCat.incl

end AlgebraicGeometry.Scheme.FiniteEtale
