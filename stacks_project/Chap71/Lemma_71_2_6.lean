module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Support
import StacksCheckRecall

/-!
# Lemma 71.2.6

A codimension-`0` point of an algebraic space that lies in the support of a
quasi-coherent module is weakly associated to that module. The same holds for a
codimension-`0` point of the scheme-theoretic support of a finite-type module.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

/- Lemma 71.2.6 (1): a codimension-zero point in the support of a quasi-coherent module
is weakly associated. -/
@[stacks 0CUL] #check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_of_codimZero_moduleSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
    {x : Points X} (hx : x ∈ F.moduleSupport) (hdim : localRingDimAt x = 0),
    x ∈ F.weakAss)

/- Lemma 71.2.6 (2): a codimension-zero point of the scheme-theoretic support of a
finite-type quasi-coherent module maps to a weakly associated point. -/
@[stacks 0CUL] #check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_of_codimZero_schemeTheoreticSupport :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    {z : Points (schemeTheoreticSupport F).X} (hdim : localRingDimAt z = 0),
    Points.map (schemeTheoreticSupport F).ι z ∈ F.weakAss)
