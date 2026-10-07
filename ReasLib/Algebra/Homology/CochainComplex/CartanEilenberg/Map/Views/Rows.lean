module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Views
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Rows
public import ReasLib.Algebra.Homology.HomologicalComplex.Image

/-!
# Rowwise views of Cartan--Eilenberg resolution maps

A resolution map induces maps on the cycles, differential images, and homology of every row.
These constructions depend only on the underlying row map; no functorial choice of auxiliary
resolutions is imposed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution.Map

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

/-- The map on horizontal cycles in bidegree `(p, q)` induced by a resolution map. -/
@[stacks 015J "row-cycles map of a Cartan-Eilenberg resolution map"]
noncomputable abbrev cyclesRow (f : Map I J) (q p : ℤ) :
    Row.cycles I q p ⟶ Row.cycles J q p :=
  HomologicalComplex.cyclesMap (row f q) p

/-- The map on horizontal differential images in bidegree `(p, q)` induced by a resolution map. -/
@[stacks 015J "row-image map of a Cartan-Eilenberg resolution map"]
noncomputable abbrev imageRow (f : Map I J) (q p : ℤ) :
    Row.image I q p ⟶ Row.image J q p :=
  HomologicalComplex.imageMap (row f q) p (p + 1)

/-- The map on horizontal homology in bidegree `(p, q)` induced by a resolution map. -/
@[stacks 015J "row-homology map of a Cartan-Eilenberg resolution map"]
noncomputable abbrev homologyRow (f : Map I J) (q p : ℤ) :
    Row.homology I q p ⟶ Row.homology J q p :=
  HomologicalComplex.homologyMap (row f q) p

/-- Row-cycles maps preserve identity resolution maps. -/
@[simp]
theorem cyclesRow_id (I : CartanEilenbergResolution K) (q p : ℤ) :
    cyclesRow (id I) q p = 𝟙 (Row.cycles I q p) := sorry

/-- Row-cycles maps preserve composition of resolution maps. -/
@[simp, reassoc]
theorem cyclesRow_comp (f : Map I J) (g : Map J N) (q p : ℤ) :
    cyclesRow (comp f g) q p = cyclesRow f q p ≫ cyclesRow g q p := sorry

/-- Row-image maps preserve identity resolution maps. -/
@[simp]
theorem imageRow_id (I : CartanEilenbergResolution K) (q p : ℤ) :
    imageRow (id I) q p = 𝟙 (Row.image I q p) := sorry

/-- Row-image maps preserve composition of resolution maps. -/
@[simp, reassoc]
theorem imageRow_comp (f : Map I J) (g : Map J N) (q p : ℤ) :
    imageRow (comp f g) q p = imageRow f q p ≫ imageRow g q p := sorry

/-- Row-homology maps preserve identity resolution maps. -/
@[simp]
theorem homologyRow_id (I : CartanEilenbergResolution K) (q p : ℤ) :
    homologyRow (id I) q p = 𝟙 (Row.homology I q p) := sorry

/-- Row-homology maps preserve composition of resolution maps. -/
@[simp, reassoc]
theorem homologyRow_comp (f : Map I J) (g : Map J N) (q p : ℤ) :
    homologyRow (comp f g) q p = homologyRow f q p ≫ homologyRow g q p := sorry

end CochainComplex.CartanEilenbergResolution.Map
