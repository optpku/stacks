/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RelativePurity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules.IsPureAlong

/-- Purity along a fibre descends from a pointed base change whose morphism is flat at
the selected point. -/
theorem of_pullback_of_flatAt {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    {S' : Scheme.{u}} (g : S' ⟶ S) (s' : S') (hpoint : g s' = s)
    (hflat : g.flatAt s')
    (hpure : ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsPureAlong
      (pullback.snd f g) s') : F.IsPureAlong f s := sorry

end Scheme.Modules.IsPureAlong

namespace Scheme.Modules.IsUniversallyPureAlong

/-- Universal purity along a fibre descends from a pointed base change whose morphism is
flat at the selected point. -/
theorem of_pullback_of_flatAt {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
    [f.FiniteType] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
    {S' : Scheme.{u}} (g : S' ⟶ S) (s' : S') (hpoint : g s' = s)
    (hflat : g.flatAt s')
    (hpure : ((Scheme.Modules.pullback (pullback.fst f g)).obj F).IsUniversallyPureAlong
      (pullback.snd f g) s') : F.IsUniversallyPureAlong f s := sorry

end Scheme.Modules.IsUniversallyPureAlong
end AlgebraicGeometry
