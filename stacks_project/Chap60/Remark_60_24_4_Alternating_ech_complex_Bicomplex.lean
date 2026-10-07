module
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_StagePDConnection
public import stacks_project.Chap60.Remark_60_24_4_Alternating_ech_complex_CrossStageCoefficients
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import stacks_project.Chap60.Remark_60_24_3_ech_complex_Cosimplicial

@[expose] public section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CrystallineModuleSheaf CechCrisCover CechCrisEnvelope
open AlgebraicGeometry.Scheme.Crystalline
universe u
namespace CrystallineSimplexPDComplex

/-- First-quadrant cohomological total-complex signs, with `ε' n = (-1)^n`. -/
instance tensorSignsUpNat : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun n : ℕ ↦ (-1 : ℤˣ) ^ n) (pow_add (-1 : ℤˣ))
  rel_add := sorry
  add_rel := sorry
  ε'_succ := sorry

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} {γA : DividedPowers IA}
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
variable {hc : ∀ (V : (Spec.{u} (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme} {c : CechCrisCover x₀}
variable (E : CechCrisEnvelope p IA γA c)
variable (hp : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [CrystallineCoefficients.SectionsCoherent I γS hc x₀ F]
variable [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsLocallyQuasiCoherent F]

/-- The displayed completed coefficient/form tensor on an actual affine
intersection simplex, with its genuine completed envelope and crystal. -/
noncomputable abbrev term (n : ℕ) (σ : Fin (n + 1) → c.Λ) (m : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of
    (CrystallineStagePDConnection.completedTensorTerm γA
      (c.simplex_hIC IA n σ) (c.simplex_hpnil p hp n σ) I γS hc x₀
      (c.simplexSpecι n σ) (c.simplexSpecι_base n σ) hI hγ
      (c.simplexSpecι_open n σ) (E.completedSimplex hp n σ) F m)

/-- The vertical differential is the actual completed stagewise crystal
connection on that simplex, including the PD exterior differential in every
positive degree. It does not invert any finite-stage projection. -/
noncomputable def differential (n : ℕ) (σ : Fin (n + 1) → c.Λ) (m : ℕ) :
    term E hp hI hγ F n σ m ⟶ term E hp hI hγ F n σ (m + 1) :=
  AddCommGrpCat.ofHom
    (CrystallineStagePDConnection.completedDifferential γA
      (c.simplex_hIC IA n σ) (c.simplex_hpnil p hp n σ) I γS hc x₀
      (c.simplexSpecι n σ) (c.simplexSpecι_base n σ) hI hγ
      (c.simplexSpecι_open n σ) (E.completedSimplex hp n σ) F m)

/-- Successive vertical maps on the actual simplex compose to zero by the
proved transport identity, without a new square-zero assumption. -/
theorem differential_comp (n : ℕ) (σ : Fin (n + 1) → c.Λ) (m : ℕ) :
    differential E hp hI hγ F n σ m ≫ differential E hp hI hγ F n σ (m + 1) = 0 := by
  apply ConcreteCategory.hom_ext
  intro x
  exact CrystallineStagePDConnection.completedDifferential_squared γA
    (c.simplex_hIC IA n σ) (c.simplex_hpnil p hp n σ) I γS hc x₀
    (c.simplexSpecι n σ) (c.simplexSpecι_base n σ) hI hγ
    (c.simplexSpecι_open n σ) (E.completedSimplex hp n σ) F m x

/-- Each actual Čech simplex supplies its own completed PD de Rham column. -/
noncomputable def column (n : ℕ) (σ : Fin (n + 1) → c.Λ) : CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of (term E hp hI hγ F n σ) (differential E hp hI hγ F n σ)
    (differential_comp E hp hI hγ F n σ)

/-- The completed tensor map along a genuine simplicial envelope map.
Coefficient restriction uses shifted geometric stages; forms use the actual
PD ring map. Both come from the same specified simplex morphism. -/
noncomputable def map {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) (q : ℕ) :
    term E hp hI hγ F n.len (reindex f σ) q ⟶ term E hp hI hγ F m.len σ q :=
  AddCommGrpCat.ofHom
    (CrystallineCrossStage.tensorMap γA
      (c.simplex_hIC IA n.len (reindex f σ)) (c.simplex_hpnil p hp n.len (reindex f σ))
      (c.simplex_hIC IA m.len σ) (c.simplex_hpnil p hp m.len σ) I γS hc x₀
      (c.simplexSpecι n.len (reindex f σ)) (c.simplexSpecι m.len σ)
      (c.simplexSpecι_base n.len (reindex f σ)) (c.simplexSpecι_base m.len σ) hI hγ
      (c.simplexSpecι_open n.len (reindex f σ)) (c.simplexSpecι_open m.len σ)
      (E.completedSimplex hp n.len (reindex f σ)) (E.completedSimplex hp m.len σ)
      (E.homDP hp f σ) (chartRestriction f σ) (E.homDP_base hp f σ)
      (E.homDP_quotient hp f σ) (chartRestriction_spec f σ) F q)

/-- The actual simplicial completed tensor map commutes with the vertical
PD de Rham differential by the cross-chart naturality statement. -/
theorem map_differential {n m : SimplexCategory} (f : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) (q : ℕ) :
    differential E hp hI hγ F n.len (reindex f σ) q ≫ map E hp hI hγ F f σ (q + 1) =
      map E hp hI hγ F f σ q ≫ differential E hp hI hγ F m.len σ q := by
  apply ConcreteCategory.hom_ext
  intro x
  exact CrystallineCrossStage.tensorMap_differential γA
    (c.simplex_hIC IA n.len (reindex f σ)) (c.simplex_hpnil p hp n.len (reindex f σ))
    (c.simplex_hIC IA m.len σ) (c.simplex_hpnil p hp m.len σ) I γS hc x₀
    (c.simplexSpecι n.len (reindex f σ)) (c.simplexSpecι m.len σ)
    (c.simplexSpecι_base n.len (reindex f σ)) (c.simplexSpecι_base m.len σ) hI hγ
    (c.simplexSpecι_open n.len (reindex f σ)) (c.simplexSpecι_open m.len σ)
    (E.completedSimplex hp n.len (reindex f σ)) (E.completedSimplex hp m.len σ)
    (E.homDP hp f σ) (chartRestriction f σ) (E.homDP_base hp f σ)
    (E.homDP_quotient hp f σ) (chartRestriction_spec f σ) F q x

/-- Reindexing by an identity leaves the actual tuple unchanged. -/
theorem reindex_identity (n : SimplexCategory) (σ : Fin (n.len + 1) → c.Λ) :
    reindex (𝟙 n) σ = σ := rfl

/-- Reindexing composes contravariantly on tuples. -/
theorem reindex_composition {l n m : SimplexCategory} (f : l ⟶ n) (g : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) : reindex f (reindex g σ) = reindex (f ≫ g) σ := rfl

/-- Although the identity cross-map starts from a deeper stage, its action
on completed tensors is the identity by compatibility of the inverse system. -/
theorem map_identity (n : SimplexCategory) (σ : Fin (n.len + 1) → c.Λ) (q : ℕ) :
    map E hp hI hγ F (𝟙 n) σ q =
      eqToHom (congrArg (fun τ ↦ term E hp hI hγ F n.len τ q) (reindex_identity n σ)) := sorry

/-- Composed face restrictions agree with the direct composite after
comparison at a common deeper source stage. This includes the different
offsets of the three completed envelopes. -/
theorem map_composition {l n m : SimplexCategory} (f : l ⟶ n) (g : n ⟶ m)
    (σ : Fin (m.len + 1) → c.Λ) (q : ℕ) :
    map E hp hI hγ F f (reindex g σ) q ≫ map E hp hI hγ F g σ q =
      eqToHom (congrArg (fun τ ↦ term E hp hI hγ F l.len τ q) (reindex_composition f g σ)) ≫
        map E hp hI hγ F (f ≫ g) σ q := sorry

variable [LinearOrder c.Λ] [Fintype c.Λ]

/-- Ordered Čech indices; only strictly increasing tuples contribute. -/
abbrev indices (n : ℕ) := {σ : Fin (n + 1) → c.Λ // StrictMono σ}

/-- Omitting a vertex preserves strict monotonicity. -/
def omitVertex {n : ℕ} (σ : indices (c := c) (n + 1)) (i : Fin (n + 2)) : indices (c := c) n :=
  ⟨reindex (SimplexCategory.δ i) σ.val, sorry⟩

/-- The finite direct sum of completed tensors, represented by its
equivalent finite product indexed by the ordered covering intersections. -/
noncomputable abbrev orderedTerm (n q : ℕ) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (∀ σ : indices (c := c) n, term E hp hI hγ F n σ.val q)

/-- The finite product of ordered completed tensors is isomorphic to the
corresponding finite direct sum, matching the source `⊕_{λ₀ < ⋯ < λₙ}` formula. -/
theorem orderedTerm_eq_directSum (n q : ℕ) :
    Nonempty
      ((orderedTerm E hp hI hγ F n q : Type u) ≃+
        DirectSum (indices (c := c) n)
          (fun σ ↦ (term E hp hI hγ F n σ.val q : Type u))) := sorry

/-- On each target tuple, the horizontal differential is the signed sum
of the actual completed tensor maps from its omitted faces. -/
noncomputable def horizontal (n q : ℕ) :
    orderedTerm E hp hI hγ F n q ⟶ orderedTerm E hp hI hγ F (n + 1) q :=
  AddCommGrpCat.ofHom (AddMonoidHom.pi fun σ ↦
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      ((map E hp hI hγ F (SimplexCategory.δ i) σ.val q).hom.comp
        (Pi.evalAddMonoidHom (fun τ : indices (c := c) n ↦ term E hp hI hγ F n τ.val q)
          (omitVertex σ i))))

/-- The vertical map is the product of the genuine completed PD de Rham
differentials on the individual ordered intersections. -/
noncomputable def vertical (n q : ℕ) :
    orderedTerm E hp hI hγ F n q ⟶ orderedTerm E hp hI hγ F n (q + 1) :=
  AddCommGrpCat.ofHom (AddMonoidHom.piMap fun σ : indices (c := c) n ↦
    (differential E hp hI hγ F n σ.val q).hom)

/-- The horizontal map has the actual alternating face formula. -/
theorem horizontal_apply (n q : ℕ)
    (x : orderedTerm E hp hI hγ F n q) (σ : indices (c := c) (n + 1)) :
    horizontal E hp hI hγ F n q x σ =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
        map E hp hI hγ F (SimplexCategory.δ i) σ.val q (x (omitVertex σ i)) := by
  simp [horizontal]
  rfl

/-- Vertical squares vanish componentwise by the proved simplex identity. -/
theorem vertical_comp (n q : ℕ) :
    vertical E hp hI hγ F n q ≫ vertical E hp hI hγ F n (q + 1) = 0 := by
  apply ConcreteCategory.hom_ext
  intro x
  funext σ
  exact ConcreteCategory.congr_hom (differential_comp E hp hI hγ F n σ.val q) (x σ)

/-- Simplicial identities for the actual face restrictions pair all terms
with opposite signs, giving the ordered Čech square-zero relation. -/
theorem horizontal_comp (n q : ℕ) :
    horizontal E hp hI hγ F n q ≫ horizontal E hp hI hγ F (n + 1) q = 0 := sorry

/-- Each face commutes with the completed PD connection; summing with
integer signs preserves that identity. -/
theorem horizontal_vertical (n q : ℕ) :
    horizontal E hp hI hγ F n q ≫ vertical E hp hI hγ F (n + 1) q =
      vertical E hp hI hγ F n q ≫ horizontal E hp hI hγ F n (q + 1) := sorry

/-- Extend the horizontal map by zero outside its cochain degree. -/
noncomputable def horizontalOrZero (n n' q : ℕ) :
    orderedTerm E hp hI hγ F n q ⟶ orderedTerm E hp hI hγ F n' q :=
  if h : n' = n + 1 then
    horizontal E hp hI hγ F n q ≫
      eqToHom (congrArg (fun k ↦ orderedTerm E hp hI hγ F k q) h.symm)
  else 0

/-- Extend the vertical map by zero outside its cochain degree. -/
noncomputable def verticalOrZero (n q q' : ℕ) :
    orderedTerm E hp hI hγ F n q ⟶ orderedTerm E hp hI hγ F n q' :=
  if h : q' = q + 1 then
    vertical E hp hI hγ F n q ≫
      eqToHom (congrArg (orderedTerm E hp hI hγ F n) h.symm)
  else 0

/-- The ordered Čech–PD de Rham bicomplex with actual completed tensor
terms, signed face restrictions, and stagewise geometric differentials. -/
noncomputable def bicomplex :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  HomologicalComplex₂.ofGradedObject (ComplexShape.up ℕ) (ComplexShape.up ℕ)
    (fun i ↦ orderedTerm E hp hI hγ F i.1 i.2)
    (horizontalOrZero E hp hI hγ F) (verticalOrZero E hp hI hγ F)
    (fun _ _ _ _ ↦ sorry) (fun _ _ _ _ ↦ sorry)
    (fun _ _ _ _ ↦ sorry) (fun _ _ _ _ ↦ sorry) (fun _ _ _ _ ↦ sorry)

/-- The ordered Čech–PD de Rham bicomplex admits a first-quadrant total complex. -/
instance hasTotal :
    HomologicalComplex₂.HasTotal (bicomplex E hp hI hγ F) (ComplexShape.up ℕ) :=
  sorry

/-- Totalization of the actual ordered Čech–PD de Rham bicomplex, using
mathlib's coproduct total complex and its cochain sign convention. -/
noncomputable def total : CochainComplex AddCommGrpCat.{u} ℕ :=
  (bicomplex E hp hI hγ F).total (ComplexShape.up ℕ)

/-- The bicomplex has the original completed-tensor objects in each degree. -/
theorem bicomplex_obj (n q : ℕ) :
    ((bicomplex E hp hI hγ F).X n).X q = orderedTerm E hp hI hγ F n q := rfl

/-- Its horizontal arrows are exactly the specified signed Čech maps. -/
theorem bicomplex_horizontal (n n' q : ℕ) :
    ((bicomplex E hp hI hγ F).d n n').f q = horizontalOrZero E hp hI hγ F n n' q := rfl

/-- Its vertical arrows are exactly the stagewise geometric PD maps. -/
theorem bicomplex_vertical (n q q' : ℕ) :
    ((bicomplex E hp hI hγ F).X n).d q q' = verticalOrZero E hp hI hγ F n q q' := rfl

end CrystallineSimplexPDComplex

namespace CechCrisEnvelope

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {IA : Ideal A} {γA : DividedPowers IA}
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
variable {hc : ∀ (V : (Spec.{u} (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme} {c : CechCrisCover x₀}
variable (E : CechCrisEnvelope p IA γA c)
variable (hp : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable (F : CrisModuleSheaf (Spec (.of A)) I γS hc X x₀)
variable [CrystallineCoefficients.SectionsCoherent I γS hc x₀ F]
variable [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsLocallyQuasiCoherent F]
variable [LinearOrder c.Λ] [Fintype c.Λ]

/-- Ordered Čech–PD de Rham bicomplex of a crystal on a finite ordered affine cover. -/
noncomputable abbrev alternatingBicomplex :
    HomologicalComplex₂ AddCommGrpCat.{u} (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  CrystallineSimplexPDComplex.bicomplex E hp hI hγ F

/-- Total complex of the ordered Čech–PD de Rham bicomplex. -/
noncomputable abbrev alternatingTotal : CochainComplex AddCommGrpCat.{u} ℕ :=
  CrystallineSimplexPDComplex.total E hp hI hγ F

/-- The total complex is mathlib's first-quadrant bicomplex totalization. -/
theorem alternatingTotal_def :
    alternatingTotal E hp hI hγ F =
      (alternatingBicomplex E hp hI hγ F).total (ComplexShape.up ℕ) := sorry

/-- Bicomplex objects are the ordered completed-tensor sums. -/
theorem alternatingBicomplex_obj (n q : ℕ) :
    ((alternatingBicomplex E hp hI hγ F).X n).X q =
      CrystallineSimplexPDComplex.orderedTerm E hp hI hγ F n q := sorry

/-- Horizontal arrows are the specified signed Čech maps. -/
theorem alternatingBicomplex_horizontal (n n' q : ℕ) :
    ((alternatingBicomplex E hp hI hγ F).d n n').f q =
      CrystallineSimplexPDComplex.horizontalOrZero E hp hI hγ F n n' q := sorry

/-- Vertical arrows are the stagewise completed PD connection maps. -/
theorem alternatingBicomplex_vertical (n q q' : ℕ) :
    ((alternatingBicomplex E hp hI hγ F).X n).d q q' =
      CrystallineSimplexPDComplex.verticalOrZero E hp hI hγ F n q q' := sorry

end CechCrisEnvelope
