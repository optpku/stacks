module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- Restricting the interior to a quasi-compact open gives a compactification
with the same proper ambient scheme. -/
def restrictOpen {Y : Scheme.{u}} {X : Over Y} [QuasiSeparatedSpace X.left]
    (P : Compactification.Of Y X) (W : X.left.Opens)
    (hW : IsCompact (W : Set X.left)) :
    Compactification.Of Y (Over.mk (W.ι ≫ X.hom)) :=
  @mk Y (Over.mk (W.ι ≫ X.hom)) P.obj.right
    (Over.homMk (W.ι ≫ ι P) (by
      change (W.ι ≫ P.obj.hom.left) ≫ P.obj.right.hom = W.ι ≫ X.hom
      rw [Category.assoc, Over.w P.obj.hom]))
    (inferInstance : IsOpenImmersion (W.ι ≫ ι P))
    (@quasiCompact_comp _ _ _ W.ι (ι P)
      (@quasiCompact_of_compactSpace _ _ W.ι
        (isCompact_iff_compactSpace.mp hW) inferInstance)
      (inferInstanceAs (QuasiCompact P.obj.hom.left)))
    inferInstance

/-- The interior immersion of the restricted compactification is the open
inclusion followed by the original interior immersion. -/
theorem restrictOpen_ι {Y : Scheme.{u}} {X : Over Y} [QuasiSeparatedSpace X.left]
    (P : Compactification.Of Y X) (W : X.left.Opens)
    (hW : IsCompact (W : Set X.left)) :
    ι (restrictOpen P W hW) = W.ι ≫ ι P := rfl

end AlgebraicGeometry.Scheme.Compactification.Of
