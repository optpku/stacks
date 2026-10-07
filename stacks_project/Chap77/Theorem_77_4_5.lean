module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Topology.LocallyFinite
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap71.Definition_71_2_2_WeakAss
public import stacks_project.Chap77.Theorem_77_4_7_FlatOver

/-!
# Finite type modules with locally finite weakly associated points

If a morphism of algebraic spaces is locally of finite presentation, a module
sheaf on the source is of finite type, and the weakly associated points of the
target are locally finite, then the relative flatness locus is open, and the
restriction of the module to that locus is finitely presented and flat over
the target.

Relative flatness uses the Comparison-side `flatOverAt`, which can be imported
together with `Y.weakAss` from Definition 71.2.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Theorem 77.4.5 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Assume
`X ⟶ Y` is locally of finite presentation, `F` is an `𝒪_X`-module of finite
type, and the set of weakly associated points of `Y` is locally finite in `Y`.
Then `U = {x ∈ |X| | flatOverAt F f x}` is open in `|X|`. -/
@[stacks 0DLR]
theorem isOpen_flatOverAt_of_locallyFinite_weakAss
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y)))) :
    IsOpen {x | flatOverAt F f x} :=
  sorry

/-- The open of `|X|` on which `F` is flat over `Y`, assuming local finiteness of
the weakly associated points of `Y`. -/
def flatOverOpens {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y)))) :
    Opens (Points X) :=
  ⟨{x | flatOverAt F f x}, isOpen_flatOverAt_of_locallyFinite_weakAss f F h_weakAss⟩

/-- Membership in `flatOverOpens f F h_weakAss` is pointwise relative flatness of
`F` over `Y`. -/
theorem mem_flatOverOpens {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y))))
    (x : Points X) :
    x ∈ flatOverOpens f F h_weakAss ↔ flatOverAt F f x :=
  sorry

/-- Theorem 77.4.5 (2): under the same hypotheses, `F|_U` is an `𝒪_U`-module of
finite presentation, where `U` is the open subspace cut out by
`flatOverOpens f F h_weakAss` and `F|_U` is `(pullback U.ι).obj F`. -/
@[stacks 0DLR]
instance flatOverLocus_isFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y)))) :
    ((pullback (OpenSubspace.ofOpens (flatOverOpens f F h_weakAss)).ι).obj F).IsFinitePresentation :=
  sorry

/-- Theorem 77.4.5 (3): under the same hypotheses, `F|_U` is flat over `Y` at every
point of `|U|`. -/
@[stacks 0DLR]
theorem flatOverLocus_isFlatOver
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun y : Y.weakAss ↦ ({y.1} : Set (Points Y)))) :
    ∀ x, flatOverAt ((pullback (OpenSubspace.ofOpens (flatOverOpens f F h_weakAss)).ι).obj F)
      ((OpenSubspace.ofOpens (flatOverOpens f F h_weakAss)).ι ≫ f) x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
