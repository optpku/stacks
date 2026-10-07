module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalProjectiveBundle
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Dual
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Excess conormal sheaf of a blowup

The exceptional square of a blowup, packaged as morphisms of `S`-schemes, and the
kernel of the canonical map `π^* C_{Z/X} ⟶ C_{E/X'}`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The closed center of an ideal sheaf, as a scheme over the same base. -/
abbrev centerOver {S : Scheme.{u}} {X : Over S} (I : X.left.IdealSheafData) : Over S :=
  Over.mk (I.subschemeι ≫ X.hom)

/-- The structure map of `centerOver` is the center immersion followed by the structure map of
`X`. -/
theorem centerOver_hom {S : Scheme.{u}} {X : Over S} (I : X.left.IdealSheafData) :
    (centerOver I).hom = I.subschemeι ≫ X.hom := sorry

/-- The underlying scheme of `centerOver` is the closed subscheme of the center. -/
theorem centerOver_left {S : Scheme.{u}} {X : Over S} (I : X.left.IdealSheafData) :
    (centerOver I).left = I.subscheme := sorry

/-- A closed subscheme of an `S`-scheme locally of finite type remains locally of finite type
over `S`. -/
instance centerOver_locallyOfFiniteType {S : Scheme.{u}} {X : Over S}
    [LocallyOfFiniteType X.hom] (I : X.left.IdealSheafData) :
    LocallyOfFiniteType (centerOver I).hom := sorry

/-- The closed immersion of the center, as a morphism of `S`-schemes. -/
def centerι {S : Scheme.{u}} {X : Over S} (I : X.left.IdealSheafData) :
    centerOver I ⟶ X :=
  Over.homMk I.subschemeι

/-- The underlying scheme morphism of `centerι` is the closed-subscheme immersion of the
center. -/
theorem centerι_left {S : Scheme.{u}} {X : Over S} (I : X.left.IdealSheafData) :
    (centerι I).left = I.subschemeι := sorry

/-- `centerι` is the over-morphism associated to the center immersion. -/
theorem centerι_eq {S : Scheme.{u}} {X : Over S} (I : X.left.IdealSheafData) :
    centerι I = Over.homMk I.subschemeι := sorry

/-- A regular closed center is locally of finite type over the ambient scheme. -/
instance centerι_locallyOfFiniteType {S : Scheme.{u}} {X : Over S}
    (I : X.left.IdealSheafData) [IsRegularImmersion I.subschemeι] :
    LocallyOfFiniteType (centerι I).left := sorry

/-- The exceptional divisor of a blowup, as a scheme over the same base. -/
abbrev exceptionalOver {S : Scheme.{u}} {X X' : Over S} (I : X.left.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b.left I] : Over S :=
  Over.mk ((I.comap b.left).subschemeι ≫ X'.hom)

/-- The structure map of `exceptionalOver` is the exceptional immersion followed by the
structure map of `X'`. -/
theorem exceptionalOver_hom {S : Scheme.{u}} {X X' : Over S} (I : X.left.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b.left I] :
    (exceptionalOver I b).hom = (I.comap b.left).subschemeι ≫ X'.hom := sorry

/-- The underlying scheme of `exceptionalOver` is the exceptional subscheme. -/
theorem exceptionalOver_left {S : Scheme.{u}} {X X' : Over S} (I : X.left.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b.left I] :
    (exceptionalOver I b).left = (I.comap b.left).subscheme := sorry

/-- The exceptional divisor of a blowup of an `S`-scheme locally of finite type remains
locally of finite type over `S`. -/
instance exceptionalOver_locallyOfFiniteType {S : Scheme.{u}} {X X' : Over S}
    [LocallyOfFiniteType X'.hom] (I : X.left.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b.left I] : LocallyOfFiniteType (exceptionalOver I b).hom := sorry

/-- The closed immersion of the exceptional divisor, as a morphism of `S`-schemes. -/
def exceptionalι {S : Scheme.{u}} {X X' : Over S} (I : X.left.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b.left I] : exceptionalOver I b ⟶ X' :=
  Over.homMk (I.comap b.left).subschemeι

/-- The underlying scheme morphism of `exceptionalι` is the exceptional closed immersion. -/
theorem exceptionalι_left {S : Scheme.{u}} {X X' : Over S} (I : X.left.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b.left I] :
    (exceptionalι I b).left = (I.comap b.left).subschemeι := sorry

/-- `exceptionalι` is the over-morphism associated to the exceptional immersion. -/
theorem exceptionalι_eq {S : Scheme.{u}} {X X' : Over S} (I : X.left.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b.left I] :
    exceptionalι I b = Over.homMk (I.comap b.left).subschemeι := sorry

/-- The exceptional immersion is locally of finite type. -/
instance exceptionalι_locallyOfFiniteType {S : Scheme.{u}} {X X' : Over S}
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I] :
    LocallyOfFiniteType (exceptionalι I b).left := sorry

/-- The exceptional projection commutes with the structure maps to the base. -/
theorem exceptionalProjection_comp_base {S : Scheme.{u}} {X X' : Over S}
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I] :
    exceptionalProjection I b.left ≫ (I.subschemeι ≫ X.hom) =
      (I.comap b.left).subschemeι ≫ X'.hom := sorry

/-- The exceptional projection of a blowup, regarded as a morphism of `S`-schemes. -/
def exceptionalProjectionOverBase {S : Scheme.{u}} {X X' : Over S}
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I] :
    exceptionalOver I b ⟶ centerOver I :=
  Over.homMk (exceptionalProjection I b.left) (exceptionalProjection_comp_base I b)

/-- The underlying scheme morphism of `exceptionalProjectionOverBase` is the canonical exceptional
projection. -/
theorem exceptionalProjectionOverBase_left {S : Scheme.{u}} {X X' : Over S}
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I] :
    (exceptionalProjectionOverBase I b).left = exceptionalProjection I b.left := sorry

/-- `exceptionalProjectionOverBase` is the over-morphism associated to the exceptional
projection. -/
theorem exceptionalProjectionOverBase_eq {S : Scheme.{u}} {X X' : Over S}
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I] :
    exceptionalProjectionOverBase I b =
      Over.homMk (exceptionalProjection I b.left)
        (exceptionalProjection_comp_base I b) := sorry

/-- The exceptional square of a blowup is cartesian. -/
theorem exceptionalSquare_isPullback {S : Scheme.{u}} {X X' : Over S}
    (I : X.left.IdealSheafData) (b : X' ⟶ X) [IsBlowup b.left I] :
    IsPullback (exceptionalι I b).left (exceptionalProjectionOverBase I b).left b.left
      (centerι I).left := sorry

/-- The excess conormal sheaf of a blowup is the kernel of the canonical map
`π^* C_{Z/X} ⟶ C_{E/X'}`. -/
def excessConormal {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] : (I.comap b).subscheme.Modules :=
  kernel (exceptionalConormalMap I b)

/-- The excess conormal sheaf is the kernel of `exceptionalConormalMap`. -/
theorem excessConormal_eq {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] : excessConormal I b = kernel (exceptionalConormalMap I b) := sorry

/-- The kernel inclusion of the excess conormal sheaf composes to zero with
`exceptionalConormalMap`. -/
theorem excessConormal_ι_comp_map {X X' : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b I] :
    kernel.ι (exceptionalConormalMap I b) ≫ exceptionalConormalMap I b = 0 := sorry

/-- Dual of the excess conormal sheaf of a blowup. -/
def excessConormalDual {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [IsBlowup b I] : (I.comap b).subscheme.Modules :=
  Scheme.Modules.dual (excessConormal I b)

/-- `excessConormalDual` is the module dual of `excessConormal`. -/
theorem excessConormalDual_eq {X X' : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b I] :
    excessConormalDual I b = Scheme.Modules.dual (excessConormal I b) := sorry

/-- For a regular closed center, the excess conormal sheaf is finite locally free. -/
instance excessConormal_isFiniteLocallyFree {X X' : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b I] [IsRegularImmersion I.subschemeι] :
    (excessConormal I b).IsFiniteLocallyFree := sorry

/-- For a regular closed center, the dual excess conormal sheaf is finite locally free. -/
instance excessConormalDual_isFiniteLocallyFree {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    [IsRegularImmersion I.subschemeι] : (excessConormalDual I b).IsFiniteLocallyFree :=
  (inferInstance : (Scheme.Modules.dual (excessConormal I b)).IsFiniteLocallyFree)

/-- The dual of an excess conormal sheaf of rank `r` has rank `r`. -/
instance excessConormalDual_isFiniteLocallyFreeOfRank {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (excessConormal I b)] :
    Scheme.Modules.IsFiniteLocallyFreeOfRank r (excessConormalDual I b) := sorry

/-- A blowup in a regular closed center is a local complete intersection morphism. -/
theorem blowup_isLocalCompleteIntersection {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    [IsRegularImmersion I.subschemeι] :
    LocallyOfType RingHom.IsLocalCompleteIntersection b := sorry

/-- For a regular closed center, the exceptional projection is smooth. -/
instance exceptionalProjection_smooth {X X' : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) [IsBlowup b I] [IsRegularImmersion I.subschemeι] :
    Smooth (exceptionalProjection I b) := sorry

/-- For a regular closed center, the exceptional projection is a local complete intersection
morphism. -/
instance exceptionalProjection_isLocalCompleteIntersection {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    [IsRegularImmersion I.subschemeι] :
    LocallyOfType RingHom.IsLocalCompleteIntersection (exceptionalProjection I b) := sorry

/-- If the excess conormal sheaf has rank `r`, the exceptional projection has relative
dimension `r`. -/
instance exceptionalProjection_relativeDimension {X X' : Scheme.{u}}
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    [IsRegularImmersion I.subschemeι] (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r (excessConormal I b)] :
    Scheme.Hom.RelativeDimension (exceptionalProjection I b) r := sorry

end AlgebraicGeometry.IsBlowup
