module

public import ReasLib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.Topology.Category.FinTopCat
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Compactness.Compact

/-!
# Finite orbits of discrete continuous actions of compact groups

The orbit class is the literal quotient by the native orbit relation. Compact
continuous orbit images are finite in the given discrete topology. Equivariant
maps act on orbit classes and restrict the supplied map to each orbit subtype.
-/

@[expose] public section
open CategoryTheory
open scoped FintypeCatDiscrete
noncomputable section
universe u
namespace CategoryTheory.DiscreteContAction.OrbitDecomposition

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable (S : DiscreteContAction TopCat.{u} G)

abbrev Carrier := S.obj.obj.V

instance carrierMulAction : MulAction G (Carrier S) := _root_.Action.instMulAction S.obj.obj

instance carrierDiscrete : DiscreteTopology (Carrier S) := S.property
instance carrierContinuous : ContinuousSMul G (Carrier S) := S.obj.property

abbrev OrbitIndex := MulAction.orbitRel.Quotient G (Carrier S)

/-- The class of a supplied point, with no representative selection. -/
abbrev indexOf (x : Carrier S) : OrbitIndex S := Quotient.mk'' x

instance orbitFiniteType (ω : OrbitIndex S) : Finite ω.orbit := by
  induction ω using Quotient.inductionOn' with
  | h x =>
    change Finite (MulAction.orbit G x)
    have h : (MulAction.orbit G x).Finite :=
      (isCompact_range (show Continuous (fun g : G ↦ g • x) from
        continuous_id.smul continuous_const)).finite_of_discrete
    exact h.to_subtype

def orbitDecomposition : Carrier S ≃ Σ ω : OrbitIndex S, ω.orbit :=
  MulAction.selfEquivSigmaOrbits' G (Carrier S)

omit [IsTopologicalGroup G] [CompactSpace G] in
@[simp]
theorem orbitDecomposition_fst (x : Carrier S) :
    (orbitDecomposition S x).1 = indexOf S x := rfl

omit [IsTopologicalGroup G] [CompactSpace G] in
@[simp]
theorem orbitDecomposition_symm_apply (x : Σ ω : OrbitIndex S, ω.orbit) :
    (orbitDecomposition S).symm x = x.2.val := rfl

def orbitAction (ω : OrbitIndex S) : Action FintypeCat.{u} G :=
  Action.FintypeCat.ofMulAction G (FintypeCat.of ω.orbit)

/-- The finite orbit inherits the supplied continuous action and discrete topology. -/
def finiteOrbit (ω : OrbitIndex S) : DiscreteContAction FintypeCat.{u} G :=
  ⟨⟨orbitAction S ω, by sorry⟩, by sorry⟩

variable {S} {T : DiscreteContAction TopCat.{u} G}

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem equivariant (f : S ⟶ T) (g : G) (x : Carrier S) :
    f.hom.hom.hom (g • x) = g • f.hom.hom.hom x :=
  ConcreteCategory.congr_hom (f.hom.hom.comm g) x

def orbitIndexMap (f : S ⟶ T) : OrbitIndex S → OrbitIndex T :=
  Quotient.map (fun x ↦ f.hom.hom.hom x) (by
    intro x y h
    obtain ⟨g, hg⟩ := h
    refine ⟨g, ?_⟩
    change g • f.hom.hom.hom y = f.hom.hom.hom x
    exact (equivariant f g y).symm.trans (congrArg (fun z : Carrier S ↦ f.hom.hom.hom z) hg))

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem orbitMap_mem (f : S ⟶ T) (ω : OrbitIndex S) (x : ω.orbit) :
    f.hom.hom.hom x.val ∈ (orbitIndexMap f ω).orbit := by
  rw [MulAction.orbitRel.Quotient.mem_orbit]
  have hx := MulAction.orbitRel.Quotient.mem_orbit.mp x.property
  change Quotient.mk'' (f.hom.hom.hom x.val) = orbitIndexMap f ω
  exact (show Quotient.mk'' (f.hom.hom.hom x.val) =
    orbitIndexMap f (Quotient.mk'' x.val) from rfl).trans (congrArg (orbitIndexMap f) hx)

def orbitMap (f : S ⟶ T) (ω : OrbitIndex S) :
    finiteOrbit S ω ⟶ finiteOrbit T (orbitIndexMap f ω) :=
  ObjectProperty.homMk (ObjectProperty.homMk
    { hom := FintypeCat.homMk (show ω.orbit → (orbitIndexMap f ω).orbit from
        fun x ↦ ⟨f.hom.hom.hom x.val, orbitMap_mem f ω x⟩)
      comm := fun g ↦ by
        apply FintypeCat.hom_ext
        intro x
        apply Subtype.ext
        exact equivariant f g x.val })

end CategoryTheory.DiscreteContAction.OrbitDecomposition
