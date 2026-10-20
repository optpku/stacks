module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.ExtensionByZero.Derived

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open OpenSubspace.Restriction

section

variable {X : RingedSpace.{u}}

-- Local declaration justification (source-local notation): these abbreviations keep the
-- Mayer--Vietoris formulas readable while naming only canonical shared derived functors.
local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DRes[" U "]" => moduleRestrictionToOpenDerived X U
local notation "DExt[" U "]" => moduleExtensionByZeroFromOpenDerived X U
local notation "DRes≤[" h "]" => derivedBetween X h
local notation "DLowerShriek[" U "]" => DRes[U] ⋙ DExt[U]
local notation "DExtAdj[" U "]" =>
  OpenSubspace.ExtensionByZero.derivedAdjunction X U

/- Domain-style sampling for Lemma 20.33.1:
- primary domain: Mayer-Vietoris distinguished triangles in `D(\mathcal O_X)` for restriction to
  opens followed by extension by zero;
- sampled owner declarations:
  `moduleRestrictionToOpenDerived`,
  `moduleExtensionByZeroFromOpenDerived`,
  `Functor.IsLeftAdjoint`,
  `derivedCompIso`,
  `Triangle.mk`,
  `distTriang`;
- best owner abstraction:
  `source-facing`: the lower-shriek Mayer-Vietoris distinguished triangle for a two-open cover;
  `core/canonical`: `DerivedCategory (RingedSpace.Modules X)`,
    `moduleRestrictionToOpenDerived`, `moduleExtensionByZeroFromOpenDerived`,
    `Functor.IsLeftAdjoint`, `derivedCompIso`,
    `Triangle.mk`, and `distTriang`;
  `bridge/view`: the theorem-local notation `DLowerShriek[U]` for the canonical composite
    `moduleRestrictionToOpenDerived X U ⋙ moduleExtensionByZeroFromOpenDerived X U`.

Primitive-vs-derived split:
- primitive data: the opens `U, V`, the cover equation `U ⊔ V = ⊤`, and the object `E`;
- derived API: theorem-level existence statements asserting that the corresponding lower-shriek edge
  morphisms occur with the expected restriction and counit formulas written directly in the theorem
  statements, rather than through a separate public predicate layer. -/

-- Proof sketch: represent `E` by a complex of `𝒪_X`-modules, apply restriction and extension by
-- zero termwise, use the classical short exact Mayer-Vietoris sequence of complexes for the cover
-- `X = U ∪ V`, and pass to the associated distinguished triangle in the derived category.
/-- Lemma 20.33.1: if a ringed space `X` is covered by two opens `U` and `V`, then every object
`E` of `D(𝒪_X)` fits into a Mayer-Vietoris distinguished triangle whose first two maps satisfy
the expected lower-shriek restriction formulas on the two projections from
`j_{U ∩ V,!}(E|_{U ∩ V})`, and the expected counit formulas on the two components of
`j_{U,!}(E|_U) ⊞ j_{V,!}(E|_V) ⟶ E`. Here `j_{W,!}` is formalized by the canonical Chapter 20
owner `moduleRestrictionToOpenDerived X W ⋙ moduleExtensionByZeroFromOpenDerived X W`. -/
@[stacks 08BU]
theorem moduleDerived_mayerVietoris_distinguishedTriangle
    (U V : Opens X.carrier)
    [(Opens.grothendieckTopology (TopCat.of U)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    [(Opens.grothendieckTopology (TopCat.of V)).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    [(Opens.grothendieckTopology (TopCat.of ((U ⊓ V : Opens X.carrier)))).PreservesSheafification
      (forget₂ CommRingCat RingCat.{u})]
    (hUV : U ⊔ V = ⊤) (E : DModX) :
    let ηU :
        (DRes[U ⊓ V]).obj E ⟶ (DRes[U ⊓ V]).obj ((DLowerShriek[U]).obj E) := by
      let η' : (DRes[U ⊓ V]).obj E ⟶ (DRes[U ⊓ V]).obj ((DLowerShriek[U]).obj E) := by
        let ηU : (DRes[U]).obj E ⟶ (DRes[U]).obj ((DLowerShriek[U]).obj E) :=
          (DExtAdj[U]).unit.app ((DRes[U]).obj E)
        let e₁ := (derivedCompIso X (inf_le_left : U ⊓ V ≤ U)).app E
        let e₂ :=
          (derivedCompIso X (inf_le_left : U ⊓ V ≤ U)).app
            ((DLowerShriek[U]).obj E)
        exact e₁.inv ≫ (DRes≤[(inf_le_left : U ⊓ V ≤ U)]).map ηU ≫ e₂.hom
      exact η'
    let ηV :
        (DRes[U ⊓ V]).obj E ⟶ (DRes[U ⊓ V]).obj ((DLowerShriek[V]).obj E) := by
      let η' : (DRes[U ⊓ V]).obj E ⟶ (DRes[U ⊓ V]).obj ((DLowerShriek[V]).obj E) := by
        let ηV : (DRes[V]).obj E ⟶ (DRes[V]).obj ((DLowerShriek[V]).obj E) :=
          (DExtAdj[V]).unit.app ((DRes[V]).obj E)
        let e₁ := (derivedCompIso X (inf_le_right : U ⊓ V ≤ V)).app E
        let e₂ :=
          (derivedCompIso X (inf_le_right : U ⊓ V ≤ V)).app
            ((DLowerShriek[V]).obj E)
        exact e₁.inv ≫ (DRes≤[(inf_le_right : U ⊓ V ≤ V)]).map ηV ≫ e₂.hom
      exact η'
    let εU : (DLowerShriek[U]).obj E ⟶ E :=
      (DExtAdj[U]).counit.app E
    let εV : (DLowerShriek[V]).obj E ⟶ E :=
      (DExtAdj[V]).counit.app E
    ∃ α : ((DLowerShriek[U ⊓ V]).obj E) ⟶ ((DLowerShriek[U]).obj E ⊞ (DLowerShriek[V]).obj E),
      ∃ β : ((DLowerShriek[U]).obj E ⊞ (DLowerShriek[V]).obj E) ⟶ E,
        ∃ δ : E ⟶ ((DLowerShriek[U ⊓ V]).obj E)⟦(1 : ℤ)⟧,
          ((DExtAdj[U ⊓ V]).homEquiv ((DRes[U ⊓ V]).obj E) ((DLowerShriek[U]).obj E))
              (α ≫ biprod.fst) = ηU ∧
            ((DExtAdj[U ⊓ V]).homEquiv ((DRes[U ⊓ V]).obj E) ((DLowerShriek[V]).obj E))
              (α ≫ biprod.snd) = ηV ∧
            biprod.inl ≫ β = εU ∧
            -(biprod.inr ≫ β) = εV ∧
            Triangle.mk α β δ ∈ distTriang DModX := sorry

end

end AlgebraicGeometry.RingedSpace
