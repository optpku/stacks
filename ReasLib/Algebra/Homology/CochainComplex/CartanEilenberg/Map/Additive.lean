/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Functor.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views.Naturality
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views.Rows.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Pages.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.PagesFunctor.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.AugmentationFunctor.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.HomologyFunctor.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.DerivedFunctor.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Total.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalFunctor.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalHomology.Preadditive

/-!
# Additive Cartan--Eilenberg map API

This facade exports the additive and preadditive computation leaves for maps of
Cartan--Eilenberg resolutions.  It owns no additional data or theorem declarations.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]

#synth Preadditive (Bundled A)
#synth (Bundled.source A).Additive
#synth (Bundled.bicomplex A).Additive
#synth (Bundled.total : Bundled A ⥤ CochainComplex A ℤ).Additive
#synth (Bundled.totalPlus : Bundled A ⥤ CochainComplex.Plus A).Additive

end CochainComplex.CartanEilenbergResolution
