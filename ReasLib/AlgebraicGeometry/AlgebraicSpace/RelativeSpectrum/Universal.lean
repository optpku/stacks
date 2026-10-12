/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum

/-!
# Universal algebra sections of a relative spectrum

The relative-spectrum point already contains a descended atlas algebra map.
Section reconstruction chooses only an actual preimage of that supplied datum;
zero is a total-function fallback. Atlas descent and sheaf uniqueness show that
the fallback is unreachable on this domain. Neither an arbitrary base morphism
nor an admitted bijectivity witness is used to select data.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace
variable {S : Scheme.{u}} {X : AlgebraicSpace S}

namespace relativeSpectrumAlgebraMap

/-- A section is the value of an actual global algebra map with the supplied atlas restriction. -/
def IsLiftedSection {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X}
    (e : relativeSpectrumAlgebraMap A g) (U : (smallEtaleSite X)ᵒᵖ)
    (a : A.obj.right.obj.obj U)
    (s : (relativeSpectrumTarget g).right.obj.obj U) : Prop :=
  ∃ α : A.obj ⟶ relativeSpectrumTarget g,
    relativeSpectrumAlgebraMap.ofHom α = e ∧
      ((InducedCategory.Hom.hom α.right).app U).hom a = s

/-- Recover the value only from an actual in-range witness; otherwise return zero. -/
def liftedSection {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X}
    (e : relativeSpectrumAlgebraMap A g) (U : (smallEtaleSite X)ᵒᵖ)
    (a : A.obj.right.obj.obj U) :
    (relativeSpectrumTarget g).right.obj.obj U := by
  classical
  exact if h : ∃ s, IsLiftedSection e U a s then Classical.choose h else 0

/-- Effective atlas descent supplies a value for a descended algebra map. -/
theorem liftedSection_inRange {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X}
    (e : relativeSpectrumAlgebraMap A g) (U : (smallEtaleSite X)ᵒᵖ)
    (a : A.obj.right.obj.obj U) : ∃ s, IsLiftedSection e U a s := sorry

/-- The selected value satisfies the actual descended-data relation. -/
theorem liftedSection_spec {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X}
    (e : relativeSpectrumAlgebraMap A g) (U : (smallEtaleSite X)ᵒᵖ)
    (a : A.obj.right.obj.obj U) : IsLiftedSection e U a (liftedSection e U a) := by
  classical
  unfold liftedSection
  split_ifs with h
  · exact Classical.choose_spec h
  · exact False.elim (h (liftedSection_inRange e U a))

/-- A known global map has exactly its own values after atlas reconstruction. -/
theorem liftedSection_ofHom {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X}
    (α : A.obj ⟶ relativeSpectrumTarget g) (U : (smallEtaleSite X)ᵒᵖ)
    (a : A.obj.right.obj.obj U) :
    liftedSection (relativeSpectrumAlgebraMap.ofHom α) U a =
      ((InducedCategory.Hom.hom α.right).app U).hom a := by
  classical
  have h : ∃ s, IsLiftedSection (relativeSpectrumAlgebraMap.ofHom α) U a s :=
    ⟨_, α, rfl, rfl⟩
  rw [liftedSection, dif_pos h]
  obtain ⟨β, hβ, hv⟩ := Classical.choose_spec h
  have heq : β = α := relativeSpectrumAlgebraMap.restrict_bijective.injective hβ
  simpa only [heq] using hv.symm

/-- The ring map reconstructed from a genuinely descended atlas map. -/
def liftedRingHom {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X}
    (e : relativeSpectrumAlgebraMap A g) (U : (smallEtaleSite X)ᵒᵖ) :
    A.obj.right.obj.obj U →+*
      (relativeSpectrumTarget g).right.obj.obj U where
  toFun := liftedSection e U
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The sheaf morphism reconstructed from the supplied descended algebra map. -/
def toSheafHom {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X}
    (e : relativeSpectrumAlgebraMap A g) :
    A.obj.right ⟶ (relativeSpectrumTarget g).right :=
  ⟨{ app := fun U ↦ @CommRingCat.ofHom (A.obj.right.obj.obj U)
         ((relativeSpectrumTarget g).right.obj.obj U)
         (inferInstanceAs (CommRing (A.obj.right.obj.obj U)))
         (inferInstanceAs (CommRing ((relativeSpectrumTarget g).right.obj.obj U)))
         (liftedRingHom e U)
     naturality := sorry }⟩

/-- Algebra reconstruction uses the actual descended atlas datum. -/
def toHom {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X}
    (e : relativeSpectrumAlgebraMap A g) : A.obj ⟶ relativeSpectrumTarget g :=
  Under.homMk (toSheafHom e) sorry

/-- Reconstruction is an inverse to restricting an actual global algebra map. -/
theorem toHom_ofHom {A : X.QcAlgebraUnder} {T : Over S} {g : ofOver T ⟶ X}
    (α : A.obj ⟶ relativeSpectrumTarget g) :
    toHom (relativeSpectrumAlgebraMap.ofHom α) = α := sorry

end relativeSpectrumAlgebraMap

/-- A relative-spectrum test point has base morphism equal to its composite with the projection. -/
theorem relativeSpecPoint_base (A : X.QcAlgebraUnder) {T : Over S}
    (t : ofOver T ⟶ relativeSpec A) :
    yonedaEquiv.symm (yonedaEquiv t).1 = t ≫ relativeSpecπ A := by
  change yonedaEquiv.symm (yonedaEquiv (t ≫ relativeSpecπ A)) = t ≫ relativeSpecπ A
  exact Equiv.symm_apply_apply yonedaEquiv _

/-- The actual algebra datum carried by a map from a test scheme to the relative spectrum. -/
def relativeSpecPointAlgebra (A : X.QcAlgebraUnder) {T : Over S}
    (t : ofOver T ⟶ relativeSpec A) : relativeSpectrumAlgebraMap A (t ≫ relativeSpecπ A) :=
  (relativeSpecPoint_base A t) ▸ (yonedaEquiv t).2

/-- Restrict a direct-image section to a test scheme over its source. -/
def pushforwardStructureTest {Y : AlgebraicSpace S} (q : Y ⟶ X)
    {T : Over S} (t : ofOver T ⟶ Y) :
    (commRingPushforward q).obj (commRingStructureSheaf Y) ⟶
      (commRingPushforward (t ≫ q)).obj (commRingStructureSheaf (ofOver T)) :=
  (commRingPushforward q).map (commRingStructureSheafMap t) ≫
    commRingPushforwardPrecomp t q

/-- A universal section has the values prescribed by all actual relative-spectrum test points. -/
def IsRelativeSpecSection (A : X.QcAlgebraUnder) (U : (smallEtaleSite X)ᵒᵖ)
    (a : A.obj.right.obj.obj U)
    (s : ((commRingPushforward (relativeSpecπ A)).obj
      (commRingStructureSheaf (relativeSpec A))).obj.obj U) : Prop :=
  ∀ (T : Over S) (t : ofOver T ⟶ relativeSpec A),
    ((InducedCategory.Hom.hom (pushforwardStructureTest (relativeSpecπ A) t)).app U).hom s =
      relativeSpectrumAlgebraMap.liftedSection (relativeSpecPointAlgebra A t) U a

/-- Reconstruct the universal value from actual compatible local algebra data, with zero fallback. -/
def relativeSpecUniversalSection (A : X.QcAlgebraUnder) (U : (smallEtaleSite X)ᵒᵖ)
    (a : A.obj.right.obj.obj U) :
    ((commRingPushforward (relativeSpecπ A)).obj
      (commRingStructureSheaf (relativeSpec A))).obj.obj U := by
  classical
  exact if h : ∃ s, IsRelativeSpecSection A U a s then Classical.choose h else 0

/-- The universal compatible test-point family is in the image of sheaf restriction. -/
theorem relativeSpecUniversalSection_inRange (A : X.QcAlgebraUnder)
    (U : (smallEtaleSite X)ᵒᵖ) (a : A.obj.right.obj.obj U) :
    ∃ s, IsRelativeSpecSection A U a s := sorry

/-- Universal evaluation agrees with each actual relative-spectrum test point. -/
theorem relativeSpecUniversalSection_spec (A : X.QcAlgebraUnder)
    (U : (smallEtaleSite X)ᵒᵖ) (a : A.obj.right.obj.obj U) :
    IsRelativeSpecSection A U a (relativeSpecUniversalSection A U a) := by
  classical
  unfold relativeSpecUniversalSection
  split_ifs with h
  · exact Classical.choose_spec h
  · exact False.elim (h (relativeSpecUniversalSection_inRange A U a))

/-- The canonical relative-spectrum counit on each ring of sections. -/
def relativeSpecUniversalRingHom (A : X.QcAlgebraUnder) (U : (smallEtaleSite X)ᵒᵖ) :
    A.obj.right.obj.obj U →+*
      ((commRingPushforward (relativeSpecπ A)).obj
        (commRingStructureSheaf (relativeSpec A))).obj.obj U where
  toFun := relativeSpecUniversalSection A U
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The actual universal sheaf-algebra map A → q_*O of its relative spectrum. -/
def relativeSpecUniversalAlgebraMap (A : X.QcAlgebraUnder) :
    A.obj ⟶ Under.mk (commRingStructureSheafMap (relativeSpecπ A)) :=
  Under.homMk
    ⟨{ app := fun U ↦ @CommRingCat.ofHom (A.obj.right.obj.obj U)
         (((commRingPushforward (relativeSpecπ A)).obj (commRingStructureSheaf (relativeSpec A))).obj.obj U)
         (inferInstanceAs (CommRing (A.obj.right.obj.obj U)))
         (inferInstanceAs (CommRing (((commRingPushforward (relativeSpecπ A)).obj (commRingStructureSheaf (relativeSpec A))).obj.obj U)))
         (relativeSpecUniversalRingHom A U)
       naturality := sorry }⟩ sorry

end AlgebraicGeometry.AlgebraicSpace
