module

public import ReasLib.AlgebraicGeometry.EllipticCurve.Family

/-!
# Composition of morphisms of elliptic curves

Cartesian zero-preserving morphisms compose along composite base maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.EllipticCurve

namespace HomOver

/-- Pasting cartesian squares of elliptic-curve morphisms yields a cartesian
square over the composite base morphism. -/
private theorem comp_isPullback {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {b : S' ⟶ S''}
    {E : Over S} {zero : S ⟶ E.left} {E' : Over S'} {zero' : S' ⟶ E'.left}
    {E'' : Over S''} {zero'' : S'' ⟶ E''.left}
    (φ : HomOver a E zero E' zero') (ψ : HomOver b E' zero' E'' zero'') :
    IsPullback (φ.hom ≫ ψ.hom) E.hom E''.hom (a ≫ b) := sorry

/-- Composite elliptic-curve morphisms send the source zero section to the
target zero section. -/
private theorem comp_comm_zero {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {b : S' ⟶ S''}
    {E : Over S} {zero : S ⟶ E.left} {E' : Over S'} {zero' : S' ⟶ E'.left}
    {E'' : Over S''} {zero'' : S'' ⟶ E''.left}
    (φ : HomOver a E zero E' zero') (ψ : HomOver b E' zero' E'' zero'') :
    zero ≫ φ.hom ≫ ψ.hom = (a ≫ b) ≫ zero'' := sorry

/-- Composition of morphisms of elliptic curves along a composite base map. -/
def comp {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {b : S' ⟶ S''}
    {E : Over S} {zero : S ⟶ E.left} {E' : Over S'} {zero' : S' ⟶ E'.left}
    {E'' : Over S''} {zero'' : S'' ⟶ E''.left}
    (φ : HomOver a E zero E' zero') (ψ : HomOver b E' zero' E'' zero'') :
    HomOver (a ≫ b) E zero E'' zero'' where
  hom := φ.hom ≫ ψ.hom
  isPullback := by exact comp_isPullback φ ψ
  comm_zero := by exact comp_comm_zero φ ψ

/-- The underlying total-space map of a composite is the composite of the
underlying maps. -/
theorem comp_hom {S S' S'' : Scheme.{u}} {a : S ⟶ S'} {b : S' ⟶ S''}
    {E : Over S} {zero : S ⟶ E.left} {E' : Over S'} {zero' : S' ⟶ E'.left}
    {E'' : Over S''} {zero'' : S'' ⟶ E''.left}
    (φ : HomOver a E zero E' zero') (ψ : HomOver b E' zero' E'' zero'') :
    (comp φ ψ).hom = φ.hom ≫ ψ.hom := rfl

end HomOver

end AlgebraicGeometry.EllipticCurve
