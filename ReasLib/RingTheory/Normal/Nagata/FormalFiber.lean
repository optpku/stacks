module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.Geometric.Reduced
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Nagata Rings and Formal Fibers

@stack 0BJ0

This leaf relates the intrinsic `NagataRing` owner to geometrically reduced formal fibers of a
Noetherian local ring. The equivalence and its two named directions form the reusable API.
-/

universe u

namespace NagataRing

/-- Lemma 15.52.4 (Tag 0BJ0): a Noetherian local ring is Nagata exactly when its formal fibers
are geometrically reduced. -/
@[stacks 0BJ0 "Nagata formal-fiber criterion"]
theorem iff_geometricallyReducedFormalFibers
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    NagataRing A ↔
      FieldAlgebraProperty.geometricallyReduced.HoldsOnFormalFibers A := sorry

/-- A Nagata local ring has geometrically reduced formal fibers. -/
@[stacks 0BJ0 "Nagata rings have geometrically reduced formal fibers"]
theorem geometricallyReducedFormalFibers
    (A : Type u) [CommRing A] [IsLocalRing A] [NagataRing A] :
    FieldAlgebraProperty.geometricallyReduced.HoldsOnFormalFibers A := sorry

/-- A Noetherian local ring with geometrically reduced formal fibers is Nagata. -/
@[stacks 0BJ0 "construct a Nagata ring from its formal fibers"]
theorem of_geometricallyReducedFormalFibers
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hA : FieldAlgebraProperty.geometricallyReduced.HoldsOnFormalFibers A) :
    NagataRing A := sorry

end NagataRing
