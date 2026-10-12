/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Right
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Topology

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Under the proper, flat, finite-presentation hypotheses, the chosen right adjoint
along the diagonal identifies the relative dualizing complex with the tensor of its
pullbacks along the two projections. -/
theorem relativeDualizingComplexIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsProper f] [Flat f]
    [Scheme.Hom.FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X)
    (c : DerivedQCoh (CategoryTheory.Limits.pullback f f) ⥤ DerivedQCoh X)
    (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (cAdjunction : pushforwardCohomologyIn (pullback.diagonal f) ⊣ c) :
    IsIsomorphic (a.obj (structureSheaf Y))
      (c.obj (tensorObj
        ((pullback (pullback.fst f f)).obj (a.obj (structureSheaf Y)))
        ((pullback (pullback.snd f f)).obj (a.obj (structureSheaf Y))))) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
