module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec

/-! # Transport of modules to a representing scheme -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The Zariski module on a representing scheme obtained by pulling an étale module back
along a representing isomorphism and applying `toScheme`. -/
noncomputable def toSchemeModule {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (e : X ≅ ofOver T) (F : X.Modules) : T.left.Modules :=
  (toScheme T).obj ((pullback e.inv).obj F)

/-- Transport to a representing scheme is the scheme comparison of pullback along the
inverse representing isomorphism. -/
theorem toSchemeModule_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    (e : X ≅ ofOver T) (F : X.Modules) :
    toSchemeModule e F = (toScheme T).obj ((pullback e.inv).obj F) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
