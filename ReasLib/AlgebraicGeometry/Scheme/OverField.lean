module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.JacobsonSpace

/-!
# Schemes and algebras over a field

This leaf provides the common slice-category spelling for schemes over the
spectrum of a field and the corresponding category of commutative algebras.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A scheme over the field `k`, packaged canonically as an object of `Over (Spec k)`. -/
@[stacks 06LH]
abbrev SchemeOverField (k : Type u) [Field k] :=
  Over (Spec (CommRingCat.of k))

/-- A commutative `k`-algebra, packaged canonically as an object of `CommAlgCat k`. -/
@[stacks 06LH]
abbrev CommAlgOverField (k : Type u) [Field k] :=
  CommAlgCat.{u} k

namespace SchemeOverField

variable {k : Type u} [Field k]

/-- The open subscheme `U ⊆ X` as a scheme over the same field. -/
noncomputable def restrictOpen (X : SchemeOverField k) (U : X.left.Opens) :
    SchemeOverField k :=
  Over.mk (U.ι ≫ X.hom)

/-- An open subscheme of a separated `k`-scheme remains separated over `k`. -/
instance isSeparated_restrictOpen_hom (X : SchemeOverField k)
    [IsSeparated X.hom] (U : X.left.Opens) :
    IsSeparated (restrictOpen X U).hom :=
  inferInstanceAs (IsSeparated (U.ι ≫ X.hom))

/-- An open subscheme of a locally finite-type `k`-scheme remains locally of
finite type over `k`. -/
instance locallyOfFiniteType_restrictOpen_hom (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (U : X.left.Opens) :
    LocallyOfFiniteType (restrictOpen X U).hom :=
  inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))

/-- An inclusion of Zariski opens induces a morphism of `k`-schemes. -/
noncomputable def restrictOpenHom (X : SchemeOverField k) {U V : X.left.Opens}
    (h : U ≤ V) : restrictOpen X U ⟶ restrictOpen X V :=
  Over.homMk (X.left.homOfLE h) (X.left.homOfLE_ι_assoc h X.hom)

/-- The underlying scheme morphism of `restrictOpenHom` is an open
immersion. -/
instance isOpenImmersion_restrictOpenHom_left (X : SchemeOverField k)
    {U V : X.left.Opens} (h : U ≤ V) :
    IsOpenImmersion (restrictOpenHom X h).left :=
  inferInstanceAs (IsOpenImmersion (X.left.homOfLE h))

/-- The open immersion of a Zariski open `U ⊆ X` as a morphism of `k`-schemes. -/
noncomputable def restrictOpenι (X : SchemeOverField k) (U : X.left.Opens) :
    restrictOpen X U ⟶ X :=
  Over.homMk U.ι

/-- The underlying scheme morphism of `restrictOpenι` is an open
immersion. -/
instance isOpenImmersion_restrictOpenι_left (X : SchemeOverField k)
    (U : X.left.Opens) :
    IsOpenImmersion (restrictOpenι X U).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

/-- The underlying scheme of the restriction to an open is its open subscheme. -/
theorem restrictOpen_left (X : SchemeOverField k) (U : X.left.Opens) :
    (restrictOpen X U).left = U.toScheme := sorry

/-- A closed point of an open subscheme of a locally finite-type scheme over a
field maps to a closed point of the ambient scheme. -/
noncomputable def closedPointEmbed (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (v : closedPoints (restrictOpen X U).left) :
    closedPoints X.left :=
  ⟨U.ι.base v.1, sorry⟩

/-- The image of a closed point of an open subscheme lies in that open. -/
theorem closedPointEmbed_mem (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (U : X.left.Opens) (v : closedPoints (restrictOpen X U).left) :
    (closedPointEmbed X U v).1 ∈ U := sorry

end SchemeOverField

end AlgebraicGeometry
