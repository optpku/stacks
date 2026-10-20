/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.CodimensionOneRamification
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiniteEtale
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-! The actual open `P¹ − {0,∞}` and its finite covers tame at both boundary DVRs. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LaurentPolynomial
open AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace MultiplicativeGroupTame

variable (k : Type u) [Field k]

/-- The two-chart intersection, with its actual projective-line boundary. -/
abbrev puncture : (ProjectiveLine.scheme k).Opens :=
  ProjectiveLine.chartX k ⊓ ProjectiveLine.chartY k

abbrev space : Scheme.{u} := (puncture k).toScheme

def structureMap : space k ⟶ Spec (.of k) :=
  (puncture k).ι ≫ ProjectiveLine.toSpec k

/-- On P¹ these are precisely the two missing rational points. -/
theorem boundary_eq : (puncture k : Set (ProjectiveLine.scheme k))ᶜ =
    {ProjectiveLine.zeroPoint k, ProjectiveLine.infinityPoint k} := by
  sorry

/-- The specified nonempty open in the integral projective line is dense. -/
theorem puncture_dense : Dense (puncture k : Set (ProjectiveLine.scheme k)) := by
  sorry

/-- Both boundary stalks of P¹ over a field are DVRs. -/
instance boundaryDVR : HasDVRBoundary (ProjectiveLine.scheme k) (puncture k) := by
  sorry

/-- The actual existing branch predicate, with neither boundary point omitted. -/
def tame : ObjectProperty (Scheme.FiniteEtale (space k)) :=
  Scheme.FiniteEtale.IsTamelyRamifiedInCodimensionOne (puncture k) (puncture_dense k)

/-- The category of actual covers, not an abstract group presentation. -/
abbrev Cover := (tame k).FullSubcategory

def inclusion : Cover k ⥤ Scheme.FiniteEtale (space k) := (tame k).ι

/-- Constants extend to a finite étale cover of all P¹, so their boundary branches
are unramified (ramification index one), hence tame. -/
theorem constants_tame (V : Scheme.FiniteEtale (Spec (.of k))) :
    tame k ((Scheme.finiteEtaleBaseChange (structureMap k)).obj V) := by
  sorry

/-- Pullback of the actual finite constant covers, bundled with its boundary property. -/
def constants : Scheme.FiniteEtale (Spec (.of k)) ⥤ Cover k :=
  (tame k).lift (Scheme.finiteEtaleBaseChange (structureMap k)) (constants_tame k)

theorem constants_forget : constants k ⋙ inclusion k =
    Scheme.finiteEtaleBaseChange (structureMap k) := rfl

theorem constants_source (V : Scheme.FiniteEtale (Spec (.of k))) :
    ((constants k).obj V).obj.left = pullback V.hom (structureMap k) := rfl

theorem constants_map (V : Scheme.FiniteEtale (Spec (.of k))) :
    ((constants k).obj V).obj.hom = pullback.snd V.hom (structureMap k) := rfl

instance connected : ConnectedSpace (space k) := by
  sorry

/-- The literal Laurent ring generator and its literal inverse. -/
def coordinateUnit : (LaurentPolynomial k)ˣ where
  val := T 1
  inv := T (-1)
  val_inv := by rw [← T_add]; exact T_zero
  inv_val := by rw [← T_add]; exact T_zero

/-- The map with homogeneous coordinates `[1:t]`, before restriction to the open. -/
def laurentToProjective : Spec (.of (LaurentPolynomial k)) ⟶ ProjectiveLine.scheme k :=
  AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (C : k →+* LaurentPolynomial k)))
    (fun _ ↦ (Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv.hom (T 1)) ≫
      (ProjectiveLine.chartXIso k).inv ≫ (ProjectiveLine.chartX k).ι

theorem laurentToProjective_range : Set.range (laurentToProjective k).base ≤
    Set.range (puncture k).ι.base := by
  sorry

/-- The specified Laurent-to-open map; invertibility of t gives the open factorization. -/
def laurentToOpen : Spec (.of (LaurentPolynomial k)) ⟶ space k :=
  IsOpenImmersion.lift (puncture k).ι (laurentToProjective k) (laurentToProjective_range k)

/-- The two projective coordinates restricted from the actual affine charts. -/
def openCoordinate : Γ(space k, ⊤)ˣ where
  val := ((ProjectiveLine.scheme k).homOfLE (U := puncture k) inf_le_left ≫
    (ProjectiveLine.chartXIso k).hom).appTop.hom
      (AffineSpace.coord (Spec (.of k)) (ULift.up (0 : Fin 1)))
  inv := ((ProjectiveLine.scheme k).homOfLE (U := puncture k) inf_le_right ≫
    (ProjectiveLine.chartYIso k).hom).appTop.hom
      (AffineSpace.coord (Spec (.of k)) (ULift.up (0 : Fin 1)))
  val_inv := by sorry
  inv_val := by sorry

def openToLaurent : space k ⟶ Spec (.of (LaurentPolynomial k)) :=
  (space k).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.eval₂ (Scheme.Hom.globalSectionsMap (structureMap k)) (openCoordinate k)))

/-- The explicit chart/evaluation maps are inverse, preserving the original Laurent model. -/
def laurentIso : Spec (.of (LaurentPolynomial k)) ≅ space k where
  hom := laurentToOpen k
  inv := openToLaurent k
  hom_inv_id := by sorry
  inv_hom_id := by sorry

theorem laurentIso_over : (laurentIso k).hom ≫ structureMap k =
    Spec.map (CommRingCat.ofHom (C : k →+* LaurentPolynomial k)) := by
  sorry

/-- A specified geometric generic point, from the actual Laurent function field. -/
def genericPoint : GeometricPoint (space k) :=
  GeometricPoint.of (AlgebraicClosure (FractionRing (LaurentPolynomial k)))
    (Spec.map (CommRingCat.ofHom
      ((algebraMap (FractionRing (LaurentPolynomial k))
        (AlgebraicClosure (FractionRing (LaurentPolynomial k)))).comp
          (algebraMap (LaurentPolynomial k) (FractionRing (LaurentPolynomial k))))) ≫
      laurentToOpen k)

end MultiplicativeGroupTame
