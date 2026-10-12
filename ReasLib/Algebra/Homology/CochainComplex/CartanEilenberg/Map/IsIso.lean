/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Functor.IsIso
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Pages
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Total.IsIso
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalHomology.IsIso
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views.IsIso

/-!
# Isomorphism API for Cartan--Eilenberg maps

This facade gathers the independent isomorphism-preservation leaves and checks the full
downstream inference chain from an isomorphism in the bundled resolution category.  Consumers
can import the smaller leaves when they only need one view.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]

section Bundled

variable {X Y : CochainComplex.CartanEilenbergResolution.Bundled A}
variable (f : X ⟶ Y) [IsIso f]
variable (p q : ℤ)

#synth IsIso f.base
#synth IsIso f.base.hom
#synth IsIso f.hom
#synth IsIso (column f p)
#synth IsIso (row f q)
#synth IsIso (term f p q)
#synth IsIso (cyclesColumn f p)
#synth IsIso (imageColumn f p)
#synth IsIso (homologyColumn f p)
#synth IsIso (cyclesRow f q p)
#synth IsIso (imageRow f q p)
#synth IsIso (homologyRow f q p)
#synth IsIso (total f)
#synth IsIso (totalPlus f)

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive]

#synth IsIso (mapped f F)
#synth IsIso (mappedRow f F q)
#synth IsIso (First.pageOne f F q)
#synth IsIso (First.pageTwo f F p q)
#synth IsIso (Second.pageOne f F q)
#synth IsIso (Second.pageTwo f F p q)
#synth IsIso (mappedTotal f F)
#synth IsIso (First.filteredTotal f F)
#synth IsIso (Second.filteredTotal f F)
#synth IsIso (mappedTotalHomology f F p)
#synth IsIso (First.filteredTotalHomology f F p)
#synth IsIso (Second.filteredTotalHomology f F p)

end Bundled

end CochainComplex.CartanEilenbergResolution.Map

