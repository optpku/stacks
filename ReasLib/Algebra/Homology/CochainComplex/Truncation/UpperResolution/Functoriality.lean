module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.UpperResolution
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of Upper-Truncation Diagrams

This leaf packages the canonical upper-truncation sequence as a functor of the
input cochain complex.  It also records arbitrary-transition formulas, so
applications need not reconstruct sequence naturality from successor maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.UpperTruncation

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Canonical upper-truncation transitions are natural in the input cochain
complex. -/
@[stacks 06XX]
theorem step_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (diagram K).map (homOfLE (Nat.le_add_right n 1)) ≫
        CochainComplex.truncLEMap f (index (n + 1)) =
      CochainComplex.truncLEMap f (index n) ≫
        (diagram L).map (homOfLE (Nat.le_add_right n 1)) := sorry

/-- A morphism of cochain complexes induces a natural transformation between
its canonical upper-truncation diagrams. -/
@[stacks 06XX]
noncomputable def diagramMap {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    diagram K ⟶ diagram L :=
  NatTrans.ofSequence
    (fun n => CochainComplex.truncLEMap f (index n))
    (step_naturality f)

/-- The component of `diagramMap f` is the canonical map between the
corresponding upper truncations. -/
@[simp, stacks 06XX]
theorem diagramMap_app {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (diagramMap f).app n = CochainComplex.truncLEMap f (index n) := sorry

/-- The upper-truncation diagram map associated to an identity is an
identity. -/
@[stacks 06XX]
theorem diagramMap_id (K : CochainComplex A ℤ) :
    diagramMap (𝟙 K) = 𝟙 (diagram K) := sorry

/-- Upper-truncation diagram maps respect composition. -/
@[stacks 06XX]
theorem diagramMap_comp {K L M : CochainComplex A ℤ}
    (f : K ⟶ L) (g : L ⟶ M) :
    diagramMap (f ≫ g) = diagramMap f ≫ diagramMap g := sorry

variable (A) in
/-- The canonical upper-truncation diagram, functorial in the input cochain
complex. -/
@[stacks 06XX]
noncomputable def diagramFunctor :
    CochainComplex A ℤ ⥤ (ℕ ⥤ CochainComplex A ℤ) where
  obj := diagram
  map := diagramMap
  map_id := diagramMap_id
  map_comp := diagramMap_comp

/-- Every transition in the canonical upper-truncation diagram is compatible
with the inclusions into the original complex. -/
@[reassoc, stacks 06XX]
theorem diagram_map_comp_ιTruncLE (K : CochainComplex A ℤ)
    {m n : ℕ} (h : m ≤ n) :
    (diagram K).map (homOfLE h) ≫ K.ιTruncLE (index n) =
      K.ιTruncLE (index m) := sorry

/-- The inclusions of the canonical upper truncations satisfy the sequence
naturality equation used to form a cocone. -/
@[stacks 06XX]
theorem targetCocone_naturality (K : CochainComplex A ℤ) (n : ℕ) :
    (diagram K).map (homOfLE (Nat.le_add_right n 1)) ≫
        K.ιTruncLE (index (n + 1)) =
      K.ιTruncLE (index n) ≫
        ((Functor.const ℕ).obj K).map (homOfLE (Nat.le_add_right n 1)) := sorry

/-- The canonical cocone from the upper truncations of a cochain complex to
the complex itself. -/
@[stacks 06XX]
noncomputable def targetCocone (K : CochainComplex A ℤ) : Cocone (diagram K) where
  pt := K
  ι := NatTrans.ofSequence
    (fun n => K.ιTruncLE (index n))
    (targetCocone_naturality K)

/-- The leg of the canonical upper-truncation cocone is the corresponding
truncation inclusion. -/
@[simp, stacks 06XX]
theorem targetCocone_ι_app (K : CochainComplex A ℤ) (n : ℕ) :
    (targetCocone K).ι.app n = K.ιTruncLE (index n) := sorry

/-- A diagram map followed by a target-cocone leg agrees with the source leg
followed by the original cochain map. -/
@[reassoc, stacks 06XX]
theorem diagramMap_app_comp_targetCocone_ι_app
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (diagramMap f).app n ≫ (targetCocone L).ι.app n =
      (targetCocone K).ι.app n ≫ f := sorry

/-- The canonical upper-truncation cocone legs are natural in the target
complex. -/
@[stacks 06XX]
theorem targetNatTrans_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (diagramFunctor A).map f ≫ (targetCocone L).ι =
      (targetCocone K).ι ≫ (Functor.const ℕ).map f := sorry

variable (A) in
/-- The canonical maps from all upper truncations to a complex, natural in
the complex. -/
@[stacks 06XX]
noncomputable def targetNatTrans :
    diagramFunctor A ⟶ Functor.const ℕ where
  app K := (targetCocone K).ι
  naturality _ _ f := targetNatTrans_naturality f

/-- The component of `targetNatTrans` is the canonical upper-truncation
target-cocone transformation. -/
@[simp, stacks 06XX]
theorem targetNatTrans_app (K : CochainComplex A ℤ) :
    (targetNatTrans A).app K = (targetCocone K).ι := sorry

/-- Evaluating `targetNatTrans` at a truncation stage gives the canonical
inclusion from that stage. -/
@[simp, stacks 06XX]
theorem targetNatTrans_app_app (K : CochainComplex A ℤ) (n : ℕ) :
    ((targetNatTrans A).app K).app n =
      K.ιTruncLE (index n) := sorry

/-- The compatibility equation used by the canonical morphism between target
cocones.  This orientation is the one expected by `CoconeMorphism.w`. -/
@[stacks 06XX]
theorem targetCoconeMap_w {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (targetCocone K).ι.app n ≫ f =
      (diagramMap f).app n ≫ (targetCocone L).ι.app n := sorry

/-- A cochain map induces the canonical morphism from the source target
cocone to the target cocone precomposed along the upper-truncation diagram
map. -/
@[stacks 06XX]
noncomputable def targetCoconeMap {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    targetCocone K ⟶
      (Cocone.precompose (diagramMap f)).obj (targetCocone L) where
  hom := f
  w := targetCoconeMap_w f

/-- The apex map of `targetCoconeMap f` is the original cochain map. -/
@[simp, stacks 06XX]
theorem targetCoconeMap_hom {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (targetCoconeMap f).hom = f := sorry

namespace Resolution

variable {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- The comparison between a resolving tower and the canonical truncation
diagram is natural for every transition, not only successors. -/
@[reassoc, stacks 06XX]
theorem comparison_naturality_of_le (S : Resolution P K)
    {m n : ℕ} (h : m ≤ n) :
    S.tower.map (homOfLE h) ≫ S.comparison.app n =
      S.comparison.app m ≫ (diagram K).map (homOfLE h) := sorry

/-- Every transition in a resolving tower is compatible with the maps to the
target complex. -/
@[reassoc (attr := simp), stacks 06XX]
theorem map_comp_toTarget (S : Resolution P K) {m n : ℕ} (h : m ≤ n) :
    S.tower.map (homOfLE h) ≫ S.toTarget n = S.toTarget m := sorry

/-- The canonical cocone of a resolution is obtained by precomposing the
upper-truncation target cocone with the resolution comparison. -/
@[stacks 06XX]
theorem cocone_eq_targetCocone_pre_comparison (S : Resolution P K) :
    S.cocone = (Cocone.precompose S.comparison).obj (targetCocone K) := sorry

end Resolution

end CochainComplex.UpperTruncation
