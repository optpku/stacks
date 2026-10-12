/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Category.TopCommRingCat
public import Mathlib.Topology.Order

/-!
# Pseudo-discrete sheaves of topological rings on schemes

On a scheme, the pseudo-discrete topology on sections of `𝒪_X` is the initial topology with
respect to restrictions to quasi-compact opens equipped with the discrete topology. This produces
a sheaf of topological commutative rings whose underlying sheaf of rings is `𝒪_X`.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat TopologicalSpace AlgebraicGeometry

namespace AlgebraicGeometry

/-- The pseudo-discrete topology on `Γ(X, U)`, initial with respect to restrictions to compact
opens equipped with the discrete topology. -/
@[reducible] def pseudoDiscreteSectionTopology (X : Scheme.{u}) (U : X.Opens) :
    TopologicalSpace Γ(X, U) :=
  ⨅ (V : X.Opens), ⨅ (_ : IsCompact (V : Set X)), ⨅ (hVU : V ≤ U),
    TopologicalSpace.induced (X.presheaf.map (homOfLE hVU).op).hom
      (⊥ : TopologicalSpace Γ(X, V))

/-- Sections of `𝒪_X` over an open, as a type carrying the pseudo-discrete topology. -/
def PseudoDiscreteSection (X : Scheme.{u}) (U : X.Opens) : Type u :=
  Γ(X, U)

/-- The pseudo-discrete section type inherits the commutative ring structure of `Γ(X, U)`. -/
instance (X : Scheme.{u}) (U : X.Opens) : CommRing (PseudoDiscreteSection X U) :=
  inferInstanceAs (CommRing Γ(X, U))

/-- The topology on `PseudoDiscreteSection X U` is the pseudo-discrete topology. -/
instance (X : Scheme.{u}) (U : X.Opens) : TopologicalSpace (PseudoDiscreteSection X U) :=
  pseudoDiscreteSectionTopology X U

/-- The pseudo-discrete topology makes section rings into topological rings. -/
instance (X : Scheme.{u}) (U : X.Opens) : IsTopologicalRing (PseudoDiscreteSection X U) :=
  sorry

/-- Restriction of pseudo-discrete sections along an inclusion of opens. -/
def pseudoDiscreteRestriction {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) :
    PseudoDiscreteSection X U →+* PseudoDiscreteSection X V :=
  (X.presheaf.map (homOfLE hVU).op).hom

/-- Restriction maps are continuous for the pseudo-discrete topology. -/
theorem continuous_pseudoDiscreteRestriction {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) :
    Continuous (pseudoDiscreteRestriction hVU) :=
  sorry

/-- Compact opens carry the discrete topology on pseudo-discrete sections. -/
theorem isDiscrete_of_isCompact {X : Scheme.{u}} {U : X.Opens} (hU : IsCompact (U : Set X)) :
    DiscreteTopology (PseudoDiscreteSection X U) :=
  sorry

/-- The pseudo-discrete presheaf of topological commutative rings on a scheme. -/
def pseudoDiscretePresheaf (X : Scheme.{u}) :
    X.carrier.Presheaf TopCommRingCat.{u} where
  obj U := TopCommRingCat.of (PseudoDiscreteSection X (unop U))
  map f := ⟨pseudoDiscreteRestriction (leOfHom (unop f)),
    continuous_pseudoDiscreteRestriction (leOfHom (unop f))⟩
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The pseudo-discrete sheaf of topological commutative rings associated to a scheme. -/
def pseudoDiscrete (X : Scheme.{u}) : X.carrier.Sheaf TopCommRingCat.{u} :=
  ⟨pseudoDiscretePresheaf X, sorry⟩

/-- A sheaf of topological rings is pseudo-discrete when compact opens have discrete sections. -/
class IsPseudoDiscrete {X : TopCat.{u}} (F : X.Sheaf TopCommRingCat.{u}) : Prop where
  /-- Sections over a compact open are discrete. -/
  discrete_on_isCompact :
    ∀ U : Opens X, IsCompact (U : Set X) → DiscreteTopology (F.presheaf.obj (op U))

/-- The canonical sheaf of topological rings on a scheme is pseudo-discrete. -/
instance (X : Scheme.{u}) : IsPseudoDiscrete (pseudoDiscrete X) := sorry

/-- The underlying type of pseudo-discrete sections over `U` is `Γ(X, U)`. -/
theorem coe_pseudoDiscrete_obj (X : Scheme.{u}) (U : X.Opens) :
    ((pseudoDiscrete X).presheaf.obj (op U) : Type u) = Γ(X, U) :=
  sorry

/-- Forgetting the topology on pseudo-discrete sections recovers the structure sheaf of `X`. -/
theorem pseudoDiscrete_forget (X : Scheme.{u}) (U : X.Opens) :
    (forget₂ TopCommRingCat CommRingCat).obj ((pseudoDiscrete X).presheaf.obj (op U)) =
      X.presheaf.obj (op U) :=
  sorry

/-- The sheafed space of topological rings obtained by endowing `𝒪_X` with the pseudo-discrete
topology. -/
def pseudoDiscreteSheafedSpace (X : Scheme.{u}) : SheafedSpace TopCommRingCat.{u} where
  carrier := X.carrier
  presheaf := pseudoDiscretePresheaf X
  IsSheaf := sorry

/-- The ring homomorphism on pseudo-discrete sections induced by a scheme morphism. -/
def pseudoDiscreteApp {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    PseudoDiscreteSection Y U →+* PseudoDiscreteSection X (f ⁻¹ᵁ U) :=
  (f.app U).hom

/-- Continuity of the component maps of a scheme morphism on pseudo-discrete sections. -/
theorem continuous_pseudoDiscreteApp {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Continuous (pseudoDiscreteApp f U) :=
  sorry

end AlgebraicGeometry
