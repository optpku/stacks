/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Representability.Local
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ZariskiTopology
public import ReasLib.CategoryTheory.Presheaf.Representability
import Mathlib.Tactic.CrossRefAttribute

/-!
# Zariski-local representability on locally ringed spaces
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w

namespace AlgebraicGeometry.LocallyRingedSpace

namespace LocalRepresentability

/-- Remark 26.15.5: a Zariski sheaf on locally ringed spaces covered locally surjectively by
scheme-representable open subfunctors is represented by a scheme. -/
@[stacks 01JK "scheme representability from a Zariski-open subfunctor cover"]
theorem isRepresentableByScheme
    (F : Sheaf zariskiTopology (Type u))
    {I : Type w} [Small.{u} I] (H : I → Subfunctor F.obj)
    (h_representable : ∀ i, (H i).IsRepresentableByScheme)
    (h_open : ∀ i, openImmersionProperty.presheaf (H i).ι)
    (h_surjective : Presheaf.IsLocallySurjective zariskiTopology
      (Limits.Sigma.desc (fun i ↦ (H i).ι))) :
    F.obj.IsRepresentableByScheme := sorry

/-- A locally surjective family of relatively representable open scheme charts is a concrete
specialization of the subfunctor-cover criterion. -/
@[stacks 01JK "scheme-chart specialization of Zariski-local representability"]
theorem isRepresentableByScheme_ofCharts
    (F : Sheaf zariskiTopology (Type u))
    {I : Type w} [Small.{u} I] (X : I → Scheme.{u})
    (f : ∀ i, yoneda.obj (X i).toLocallyRingedSpace ⟶ F.obj)
    (h_open : ∀ i, openImmersionProperty.presheaf (f i))
    (h_surjective : Presheaf.IsLocallySurjective zariskiTopology
      (Limits.Sigma.desc f)) :
    F.obj.IsRepresentableByScheme := sorry

end LocalRepresentability

end AlgebraicGeometry.LocallyRingedSpace
