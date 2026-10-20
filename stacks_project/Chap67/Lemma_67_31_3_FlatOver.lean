module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import stacks_project.Chap66.«66_26_1_1_Restrict»
public import stacks_project.Chap66.Definition_66_18_9_Square
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Relative flatness of quasi-coherent modules on algebraic spaces

A quasi-coherent module on an algebraic space is flat at a point over the target when some
étale scheme presentation reduces the condition to `Scheme.Modules.flatOverAt`. Restriction
along an étale scheme object is the composite of étale module restriction with the comparison
from the small étale ringed site of `ofOver U` to modules on the underlying scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Pointwise relative flatness unpacks as the existence of an étale scheme presentation whose
restricted module is relatively flat at a germ mapping to the given point. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    (x : Points X),
    flatOverAt F f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
        (ha : Etale a) (hb : Etale b),
        a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U u) = x ∧
            Scheme.Modules.flatOverAt
              ((@restrictFunctor S (ofOver U) X a ha ⋙ restrictToScheme U).obj F) h.left u)

/- Global relative flatness is the pointwise condition at every point of the source. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOver_iff_forall_flatOverAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y),
    flatOver F f ↔ ∀ x : Points X, flatOverAt F f x)

end AlgebraicGeometry.AlgebraicSpace.Modules
