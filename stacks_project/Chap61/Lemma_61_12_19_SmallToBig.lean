/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.SmallToBig
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

/-! Compatibility checks for the promoted small-to-big pro-étale API. -/

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 61.12.19 - small-to-big pro-étale compatibility. -/
#check (AlgebraicGeometry.Scheme.ProEt.SmallToBig.relocalizationFunctor :
  ∀ {S T : Scheme.{u}}, (T ⟶ S) → T.ProEt ⥤ Over S)

#check (AlgebraicGeometry.Scheme.ProEt.SmallToBig.inverseImage :
  ∀ {S T : Scheme.{u}} (f : T ⟶ S),
    Sheaf (Scheme.proetaleTopology.{u}.over S) (Type (u + 1)) ⥤
      Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) (Type (u + 1)))

#check (AlgebraicGeometry.Scheme.ProEt.SmallToBig.inverseImage_obj_obj :
    ∀ {S T : Scheme.{u}} (f : T ⟶ S)
    (𝒢 : Sheaf (Scheme.proetaleTopology.{u}.over S) (Type (u + 1)))
    (U : T.ProEt),
    ((AlgebraicGeometry.Scheme.ProEt.SmallToBig.inverseImage f).obj 𝒢).1.obj
        (Opposite.op U) =
      𝒢.1.obj (Opposite.op
        ((AlgebraicGeometry.Scheme.ProEt.SmallToBig.relocalizationFunctor f).obj U)))
