module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.SchemePushforward

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 86.10.1: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
quasi-compact and quasi-separated algebraic spaces over `S`. Assume `X` and `Y`
are representable, and let `f0 : X0 ⟶ Y0` be a morphism of schemes representing
`f`. Let `a` be a right adjoint of `Rf_*` from Lemma 86.3.1, and let `a0` be a
right adjoint of `Rf_*` from Duality for Schemes, Lemma 48.3.1. Then the square
commutes under the canonical equivalences of Derived Categories of Spaces,
Lemma 071Q: `a0 ⋙ schemeToSpaceDerived X0` is naturally isomorphic to
`schemeToSpaceDerived Y0 ⋙ a`. This follows from uniqueness of adjoints and the
compatibilities of Derived Categories of Spaces, Remark 75.6.3. -/
@[stacks 0E6E] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.ofOver_rightAdjoint_comm :
    ∀ {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [CompactSpace X0.left] [QuasiSeparatedSpace X0.left]
    [CompactSpace Y0.left] [QuasiSeparatedSpace Y0.left]
    [QuasiCompact (ofOverMap f0)] [QuasiSeparated (ofOverMap f0)]
    (a0 : Scheme.DerivedQCoh Y0.left ⥤ Scheme.DerivedQCoh X0.left)
    (a : DerivedQCoh (ofOver Y0) ⥤ DerivedQCoh (ofOver X0))
    (adj0 : Scheme.DerivedQCoh.pushforwardCohomologyIn f0.left ⊣ a0)
    (adj : pushforwardCohomologyIn (ofOverMap f0) ⊣ a),
    IsIsomorphic (a0 ⋙ schemeToSpaceDerived X0) (schemeToSpaceDerived Y0 ⋙ a))

/- Objectwise form of the comparison of right adjoints of derived pushforward along a
representing morphism of schemes. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.ofOver_rightAdjoint_comm_app :
    ∀ {S : Scheme.{u}} {X0 Y0 : Over S} (f0 : X0 ⟶ Y0)
    [CompactSpace X0.left] [QuasiSeparatedSpace X0.left]
    [CompactSpace Y0.left] [QuasiSeparatedSpace Y0.left]
    [QuasiCompact (ofOverMap f0)] [QuasiSeparated (ofOverMap f0)]
    (a0 : Scheme.DerivedQCoh Y0.left ⥤ Scheme.DerivedQCoh X0.left)
    (a : DerivedQCoh (ofOver Y0) ⥤ DerivedQCoh (ofOver X0))
    (adj0 : Scheme.DerivedQCoh.pushforwardCohomologyIn f0.left ⊣ a0)
    (adj : pushforwardCohomologyIn (ofOverMap f0) ⊣ a)
    (K : Scheme.DerivedQCoh Y0.left),
    IsIsomorphic ((schemeToSpaceDerived X0).obj (a0.obj K))
      (a.obj ((schemeToSpaceDerived Y0).obj K)))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
