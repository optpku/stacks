/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.LocalEquivalence
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_11_2
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stackification and pullback of modules

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that
induces an equivalence of stackifications yields equivalences on sheaves of
modules and on quasi-coherent modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/-- Pullback of modules along a 1-morphism of categories fibred in groupoids
sends quasi-coherent sheaves to quasi-coherent sheaves. -/
theorem modulePullback_le_inverseImage :
    quasiCoherentModuleProperty Y ≤
      (quasiCoherentModuleProperty X).inverseImage (modulePullback f) :=
  sorry

namespace QCoh

/-- Restriction of `modulePullback f` to quasi-coherent modules. -/
def pullback : QCoh Y ⥤ QCoh X :=
  ObjectProperty.FullSubcategory.restrict (modulePullback f)
    (modulePullback_le_inverseImage f)

/-- The underlying module sheaf of `QCoh.pullback f` is `modulePullback f`. -/
theorem pullback_obj (G : QCoh Y) :
    ((pullback f).obj G).obj = (modulePullback f).obj G.obj :=
  sorry

end QCoh

/-- Lemma 96.13.2 (1): let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `f` induces an equivalence of stackifications,
meaning `Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f`, then
`f^* = modulePullback f : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` is an equivalence. -/
@[stacks 06WR]
theorem modulePullback_isEquivalence
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f) :
    (modulePullback f).IsEquivalence :=
  sorry

/-- Lemma 96.13.2 (2): let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `f` induces an equivalence of stackifications,
meaning `Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f`, then
`QCoh.pullback f : QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)` is an equivalence. -/
@[stacks 06WR]
theorem QCoh.pullback_isEquivalence
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f) :
    (QCoh.pullback f).IsEquivalence :=
  sorry

/-- If the pullback of a module sheaf along a local equivalence of stackifications
is quasi-coherent, then the original sheaf is quasi-coherent. -/
theorem isQuasicoherent_of_modulePullback
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f)
    (G : SheafOfModules.{u} (structureSheaf Y))
    [((modulePullback f).obj G).IsQuasicoherent] :
    G.IsQuasicoherent :=
  sorry

/-- Quasi-coherence of a module sheaf is equivalent to quasi-coherence of its
pullback along a 1-morphism inducing an equivalence of stackifications. -/
theorem modulePullback_isQuasicoherent_iff
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f)
    (G : SheafOfModules.{u} (structureSheaf Y)) :
    ((modulePullback f).obj G).IsQuasicoherent ↔ G.IsQuasicoherent :=
  sorry

/-- Specialization of the module pullback equivalence to a stackification
1-morphism. -/
theorem modulePullback_isEquivalence_of_isStackification
    (hstack : Hom.IsStackification (Scheme.fppfTopology.over S) f) :
    (modulePullback f).IsEquivalence :=
  sorry

/-- Specialization of the quasi-coherent pullback equivalence to a
stackification 1-morphism. -/
theorem QCoh.pullback_isEquivalence_of_isStackification
    (hstack : Hom.IsStackification (Scheme.fppfTopology.over S) f) :
    (QCoh.pullback f).IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
