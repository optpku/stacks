module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_6_RankLocus

/-!
# Relatively perfect derived modules on algebraic spaces

An object of `D(𝒪_X)` is `Y`-perfect when it is pseudo-coherent and, after restriction
to `f⁻¹𝒪_Y`, locally of finite Tor dimension. The Tor conjunct is tested on étale
scheme charts, avoiding the `UnivLE`-gated ringed-site Tor-dimension predicate.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A derived `𝒪_X`-module locally has finite Tor dimension over `f⁻¹𝒪_Y` when, on every
étale scheme chart square over `f`, the transported restriction to the source chart
locally has finite Tor dimension after restriction to `h.left⁻¹𝒪_V`. -/
def locallyFiniteTorDimensionOver (f : X ⟶ Y) :
    ObjectProperty (ModuleDerived X) :=
  fun E ↦
    ∀ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y) (h : U ⟶ V)
      [AlgebraicSpace.Etale φ] [AlgebraicSpace.Etale ψ],
      φ ≫ f = ofOverMap h ≫ ψ →
        RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension
          ((RingedSpace.ModuleDerived.relativeRestriction h.left.toShHom).obj
            (Eq.mp (derivedCategory_modules_eq_ringedSpace U.left)
              ((restrictToSchemeDerived U).obj ((pullback φ).obj E))))

/-- The object property of being perfect relative to a flat, locally finitely presented
morphism of algebraic spaces. -/
def perfectRelativeTo (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    ObjectProperty (ModuleDerived X) :=
  (fun E ↦ IsPseudoCoherent X E) ⊓ locallyFiniteTorDimensionOver f

/-- A derived `𝒪_X`-module is `Y`-perfect when it belongs to `perfectRelativeTo f`. -/
abbrev IsPerfectRelativeTo (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (E : ModuleDerived X) : Prop :=
  perfectRelativeTo f E

/-- Relative perfectness over a flat, locally finitely presented morphism `f : X ⟶ Y`
is equivalent to pseudo-coherence on `𝒪_X` and local finite Tor dimension as an object
of `D(f⁻¹𝒪_Y)`. -/
theorem isPerfectRelativeTo_iff (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f]
    (E : ModuleDerived X) :
    IsPerfectRelativeTo f E ↔
      IsPseudoCoherent X E ∧ locallyFiniteTorDimensionOver f E := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
