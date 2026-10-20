module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Rees
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Twist

/-!
# Blowups of algebraic spaces in quasi-coherent ideal sheaves

A chosen blowup of an algebraic space `X` in a quasi-coherent ideal sheaf `I`
is a relative projective spectrum of the Rees algebra of `I`. The center is the
closed subspace cut out by `I`, and the exceptional divisor is the inverse image
of that center.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open RelativeProj

/-- A chosen blowup of `X` in the quasi-coherent ideal sheaf `I`, presented as
the relative projective spectrum of the Rees algebra `⊕_{n ≥ 0} I ^ n`. -/
abbrev Blowup {S : Scheme.{u}} (X : AlgebraicSpace S)
    (I : IdealSubobject X) [IsQuasiCoherent I] :=
  RelativeProj.Twist (reesAlgebra I) (reesDegreePieces I)

namespace Blowup

/-- The relative-Proj presentation of a blowup as the Proj of its Rees algebra. -/
def reesTwist {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (π : Blowup X I) :
    RelativeProj.Twist (reesAlgebra I) (reesDegreePieces I) :=
  π

/-- Package a relative-Proj presentation of the Rees algebra of `I` as a chosen
blowup of `X` in `I`. -/
def of {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (P : Twist (reesAlgebra I) (reesDegreePieces I)) :
    Blowup X I :=
  P

/-- `Blowup.of` stores the given relative-Proj presentation. -/
theorem of_reesTwist {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I]
    (P : Twist (reesAlgebra I) (reesDegreePieces I)) :
    (of P).reesTwist = P :=
  rfl

/-- The algebraic space `P = underline{Proj}_X(⊕_{n ≥ 0} I ^ n)`. -/
abbrev space {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (π : Blowup X I) : AlgebraicSpace S :=
  π.reesTwist.space

/-- The space of a blowup is the space of its relative-Proj presentation. -/
theorem space_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (π : Blowup X I) :
    π.space = π.reesTwist.space :=
  rfl

/-- The structure morphism `b : P ⟶ X` of a blowup. -/
abbrev hom {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (π : Blowup X I) : π.space ⟶ X :=
  π.reesTwist.π

/-- The blowup morphism is the structure map of `underline{Proj}_X(⊕_{n ≥ 0} I ^ n)`. -/
theorem hom_eq_π {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (π : Blowup X I) :
    π.hom = π.reesTwist.π :=
  rfl

/-- The blowup as an object of the slice category over `X`. -/
def toOver {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (π : Blowup X I) : Over X :=
  Over.mk π.hom

/-- The slice morphism of `toOver π` is the blowup morphism. -/
theorem toOver_hom {S : Scheme.{u}} {X : AlgebraicSpace S} {I : IdealSubobject X}
    [IsQuasiCoherent I] (π : Blowup X I) :
    (toOver π).hom = π.hom :=
  rfl

/-- The center of the blowup of `X` in `I` is the closed subspace corresponding
to `I`. -/
noncomputable def center {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] : ClosedSubspace X :=
  ClosedSubspace.ofQuasiCoherentIdeal I

/-- The center of a blowup in `I` is the closed subspace cut out by `I`. -/
theorem center_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    center I = ClosedSubspace.ofQuasiCoherentIdeal I :=
  rfl

/-- The inclusion of the center is the closed immersion cut out by `I`. -/
theorem center_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    (center I).ι = subschemeι I :=
  rfl

/-- The exceptional divisor of a blowup is the inverse image of the center. -/
noncomputable def exceptionalDivisor {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I) :
    ClosedSubspace π.space :=
  (center I).inverseImageSubspace π.hom

/-- The inclusion of the exceptional divisor is the inverse-image immersion of
the center. -/
theorem exceptionalDivisor_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I) :
    (exceptionalDivisor π).ι = inverseImageι π.hom (subschemeι I) :=
  rfl

/-- The exceptional divisor is the inverse image of the center along the
blowup morphism. -/
theorem exceptionalDivisor_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I) :
    exceptionalDivisor π = (center I).inverseImageSubspace π.hom :=
  rfl

/-- The blowing up of `X` along a closed subspace `Z` is the blowup in the
quasi-coherent ideal sheaf of `Z`. -/
abbrev along {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) :=
  @Blowup S X Z.idealSheaf
    (@Hom.instIsQuasiCoherent_idealSheafSubobject S Z.X X Z.ι Z.isClosedImmersion)

/-- The underlying algebraic space of the blowup along a closed subspace. -/
abbrev alongSpace {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) : AlgebraicSpace S :=
  RelativeProj.Twist.space π

/-- The structure morphism of the blowup along a closed subspace. -/
abbrev alongHom {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    (π : along Z) : alongSpace Z π ⟶ X :=
  RelativeProj.Twist.π π

/-- Blowing up along `Z` is blowing up in the ideal sheaf of `Z`. -/
theorem along_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    [IsQuasiCoherent Z.idealSheaf] :
    along Z = Blowup X Z.idealSheaf :=
  rfl

end Blowup

end AlgebraicGeometry.AlgebraicSpace
