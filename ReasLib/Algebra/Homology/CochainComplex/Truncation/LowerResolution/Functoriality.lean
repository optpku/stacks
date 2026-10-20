/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution

/-!
# Functoriality of Lower-Truncation Diagrams

This leaf packages the canonical lower-truncation inverse system as a functor
of the input cochain complex.  It also exposes arbitrary-transition formulas
and the factorization of a resolution cone through the canonical source cone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe v u

namespace CochainComplex.LowerTruncation

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The successor maps of canonical lower-truncation diagrams are natural in the input cochain
complex. -/
@[stacks 070F]
theorem step_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (diagram K).map (homOfLE (Nat.le_add_right n 1)).op ≫
      CochainComplex.truncGEMap f (index n) =
        CochainComplex.truncGEMap f (index (n + 1)) ≫
          (diagram L).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- A morphism of cochain complexes induces a natural transformation between
its canonical lower-truncation inverse systems. -/
@[stacks 070F]
noncomputable def diagramMap {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    diagram K ⟶ diagram L :=
  NatTrans.ofOpSequence
    (fun n => CochainComplex.truncGEMap f (index n))
    (step_naturality f)

/-- The component of `diagramMap f` is the canonical map between the
corresponding lower truncations. -/
@[simp, stacks 070F]
theorem diagramMap_app {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (diagramMap f).app (op n) = CochainComplex.truncGEMap f (index n) := sorry

/-- The lower-truncation diagram map associated to an identity is an
identity. -/
@[stacks 070F]
theorem diagramMap_id (K : CochainComplex A ℤ) :
    diagramMap (𝟙 K) = 𝟙 (diagram K) := sorry

/-- Lower-truncation diagram maps respect composition. -/
@[stacks 070F]
theorem diagramMap_comp {K L M : CochainComplex A ℤ}
    (f : K ⟶ L) (g : L ⟶ M) :
    diagramMap (f ≫ g) = diagramMap f ≫ diagramMap g := sorry

variable (A) in
/-- The canonical lower-truncation inverse system, functorial in the input
cochain complex. -/
@[stacks 070F]
noncomputable def diagramFunctor :
    CochainComplex A ℤ ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ) where
  obj := diagram
  map := diagramMap
  map_id := diagramMap_id
  map_comp := diagramMap_comp

/-- Every transition in the canonical lower-truncation diagram is compatible
with the projections from the original complex. -/
@[reassoc, stacks 070F]
theorem πTruncGE_comp_diagram_map (K : CochainComplex A ℤ)
    {m n : ℕ} (h : m ≤ n) :
    K.πTruncGE (index n) ≫ (diagram K).map (homOfLE h).op =
      K.πTruncGE (index m) := sorry

/-- The projections to the canonical lower truncations satisfy the sequence
naturality equation used to form a cone. -/
@[stacks 070F]
theorem sourceCone_naturality (K : CochainComplex A ℤ) (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj K).map (homOfLE (Nat.le_add_right n 1)).op ≫
        K.πTruncGE (index n) =
      K.πTruncGE (index (n + 1)) ≫
        (diagram K).map (homOfLE (Nat.le_add_right n 1)).op := sorry

/-- The canonical cone from a cochain complex to its lower truncations. -/
@[stacks 070F]
noncomputable def sourceCone (K : CochainComplex A ℤ) : Cone (diagram K) where
  pt := K
  π := NatTrans.ofOpSequence
    (fun n => K.πTruncGE (index n))
    (sourceCone_naturality K)

/-- The projection of the canonical lower-truncation cone is the
corresponding truncation map. -/
@[simp, stacks 070F]
theorem sourceCone_π_app (K : CochainComplex A ℤ) (n : ℕ) :
    (sourceCone K).π.app (op n) = K.πTruncGE (index n) := sorry

/-- A source-cone leg followed by a diagram-map component agrees with the
original cochain map followed by the target source-cone leg. -/
@[reassoc, stacks 070F]
theorem sourceCone_π_app_comp_diagramMap_app
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    (sourceCone K).π.app (op n) ≫ (diagramMap f).app (op n) =
      f ≫ (sourceCone L).π.app (op n) := sorry

/-- The canonical lower-truncation cone legs are natural in the source
complex. -/
@[stacks 070F]
theorem sourceNatTrans_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (Functor.const ℕᵒᵖ).map f ≫ (sourceCone L).π =
      (sourceCone K).π ≫ (diagramFunctor A).map f := sorry

variable (A) in
/-- The canonical maps from a complex to all of its lower truncations,
natural in the complex. -/
@[stacks 070F]
noncomputable def sourceNatTrans :
    Functor.const ℕᵒᵖ ⟶ diagramFunctor A where
  app K := (sourceCone K).π
  naturality _ _ f := sourceNatTrans_naturality f

/-- The component of `sourceNatTrans` is the canonical lower-truncation
source-cone transformation. -/
@[simp, stacks 070F]
theorem sourceNatTrans_app (K : CochainComplex A ℤ) :
    (sourceNatTrans A).app K = (sourceCone K).π := sorry

/-- Evaluating `sourceNatTrans` at a truncation stage gives the canonical
projection to that stage. -/
@[simp, stacks 070F]
theorem sourceNatTrans_app_app (K : CochainComplex A ℤ) (n : ℕ) :
    ((sourceNatTrans A).app K).app (op n) =
      K.πTruncGE (index n) := sorry

/-- The compatibility equation used by the canonical morphism between source
cones.  This orientation is the one expected by `ConeMorphism.w`. -/
@[stacks 070F]
theorem sourceConeMap_w {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℕ) :
    f ≫ (sourceCone L).π.app (op n) =
      (sourceCone K).π.app (op n) ≫ (diagramMap f).app (op n) := sorry

/-- A cochain map induces the canonical morphism from its source cone,
postcomposed along the lower-truncation diagram map, to the target source
cone. -/
@[stacks 070F]
noncomputable def sourceConeMap {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (Cone.postcompose (diagramMap f)).obj (sourceCone K) ⟶ sourceCone L where
  hom := f
  w j := sourceConeMap_w f j.unop

/-- The apex map of `sourceConeMap f` is the original cochain map. -/
@[simp, stacks 070F]
theorem sourceConeMap_hom {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (sourceConeMap f).hom = f := sorry

namespace Resolution

variable {P : ObjectProperty A} {K : CochainComplex A ℤ}

/-- The comparison from canonical truncations to a resolving tower is natural
for every transition, not only successors. -/
@[reassoc, stacks 070F]
theorem comparison_naturality_of_le (S : Resolution P K)
    {m n : ℕ} (h : m ≤ n) :
    (diagram K).map (homOfLE h).op ≫ S.comparison.app (op m) =
      S.comparison.app (op n) ≫ S.tower.map (homOfLE h).op := sorry

/-- Every transition in a resolving tower is compatible with the maps from
the source complex. -/
@[reassoc (attr := simp), stacks 070F]
theorem fromSource_comp_map (S : Resolution P K) {m n : ℕ} (h : m ≤ n) :
    S.fromSource n ≫ S.tower.map (homOfLE h).op = S.fromSource m := sorry

/-- The canonical cone of a resolution is obtained by postcomposing the
lower-truncation source cone with the resolution comparison. -/
@[stacks 070F]
theorem cone_eq_sourceCone_postcompose_comparison (S : Resolution P K) :
    S.cone = (Cone.postcompose S.comparison).obj (sourceCone K) := sorry

end Resolution

end CochainComplex.LowerTruncation
