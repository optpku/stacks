module

public import ReasLib.CategoryTheory.Fibered.Groupoids.LocalEquivalence
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import stacks_project.Chap96.Definition_96_11_1_QCoh
public import stacks_project.Chap96.Lemma_96_11_2
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Stackification
import StacksCheckRecall

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

#check (AlgebraicGeometry.GroupoidsOver.modulePullback_le_inverseImage :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    quasiCoherentModuleProperty Y ≤
      (quasiCoherentModuleProperty X).inverseImage (modulePullback f))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.pullback :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y),
    QCoh Y ⥤ QCoh X)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.pullback_obj :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (G : QCoh Y),
    ((QCoh.pullback f).obj G).obj = (modulePullback f).obj G.obj)

/- Lemma 96.13.2 (1): let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `f` induces an equivalence of stackifications,
meaning `Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f`, then
`f^* = modulePullback f : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` is an equivalence. -/
@[stacks 06WR] #check (AlgebraicGeometry.GroupoidsOver.modulePullback_isEquivalence :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f),
    (modulePullback f).IsEquivalence)

/- Lemma 96.13.2 (2): let `f : X ⟶ Y` be a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. If `f` induces an equivalence of stackifications,
meaning `Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f`, then
`QCoh.pullback f : QCoh(𝒪_Y) ⥤ QCoh(𝒪_X)` is an equivalence. -/
@[stacks 06WR] #check (AlgebraicGeometry.GroupoidsOver.QCoh.pullback_isEquivalence :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f),
    (QCoh.pullback f).IsEquivalence)

#check (AlgebraicGeometry.GroupoidsOver.isQuasicoherent_of_modulePullback :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f)
    (G : SheafOfModules.{u} (structureSheaf Y))
    [((modulePullback f).obj G).IsQuasicoherent],
    G.IsQuasicoherent)

#check (AlgebraicGeometry.GroupoidsOver.modulePullback_isQuasicoherent_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f)
    (G : SheafOfModules.{u} (structureSheaf Y)),
    ((modulePullback f).obj G).IsQuasicoherent ↔ G.IsQuasicoherent)

#check (AlgebraicGeometry.GroupoidsOver.modulePullback_isEquivalence_of_isStackification :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hstack : Hom.IsStackification (Scheme.fppfTopology.over S) f),
    (modulePullback f).IsEquivalence)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.pullback_isEquivalence_of_isStackification :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (hstack : Hom.IsStackification (Scheme.fppfTopology.over S) f),
    (QCoh.pullback f).IsEquivalence)

end AlgebraicGeometry.GroupoidsOver
