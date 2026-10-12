/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Existence
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.CalculusOfFractions

/-!
# Localization of compactifications
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- The full subcategory of schemes over `S` which admit a compactification. -/
abbrev CompactifiableOver (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun X : Over S ↦ Nonempty (Of S X))

/-- Regard a compactification as a fixed-interior compactification of its open part. -/
def toOf (S : Scheme.{u}) (P : Compactification S) : Of S ((openPart S).obj P) :=
  ⟨Under.mk P.obj.hom,
    { isOpenImmersion := P.property.isOpenImmersion
      quasiCompact := P.property.quasiCompact
      isProper := P.property.isProper }⟩

/-- The fixed-interior compactification obtained from `P` has the original interior arrow. -/
theorem toOf_hom (S : Scheme.{u}) (P : Compactification S) :
    (toOf S P).obj.hom = P.obj.hom := sorry

/-- The functor sending a compactification to its open part over `S`. -/
def toCompactifiable (S : Scheme.{u}) : Compactification S ⥤ CompactifiableOver S :=
  ObjectProperty.lift (fun X : Over S ↦ Nonempty (Of S X))
    (openPart S) (fun P ↦ ⟨toOf S P⟩)

/-- The open part underlying `toCompactifiable S` agrees with `openPart S`. -/
theorem toCompactifiable_obj (S : Scheme.{u}) (P : Compactification S) :
    ((toCompactifiable S).obj P).obj = (openPart S).obj P := sorry

/-- For a quasi-compact quasi-separated scheme `S`, the open-part functor is a localization
at compactification morphisms inducing isomorphisms on their open parts. -/
instance toCompactifiableIsLocalization (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] :
    (toCompactifiable S).IsLocalization (interiorIsomorphisms S) := sorry

end AlgebraicGeometry.Scheme.Compactification
