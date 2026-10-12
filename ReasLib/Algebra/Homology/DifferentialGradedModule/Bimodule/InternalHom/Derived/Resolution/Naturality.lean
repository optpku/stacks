/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Naturality
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Resolution
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.Resolution.Map
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of resolution models for derived internal Hom

The resolution-model comparison is contravariantly natural in the bimodule source and
covariantly natural in compatible maps of property-(I) resolutions.  The latter consumes a
`DifferentialGradedModule.PropertyI.Resolution.Map`, keeping the comparison square bundled at
the resolution layer rather than repeating a bare morphism and equation downstream.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedBimodule.InternalHom.Derived.Resolution

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, v} R}

/-- The forward resolution-model comparison is covariantly natural in compatible maps of
property-(I) resolutions. -/
@[reassoc, stacks 0CS5 "target naturality of the property-I derived internal-Hom model"]
theorem modelIso_hom_naturality_target
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M N : DifferentialGradedModule.{u, v} B} {f : M ⟶ N}
    {I : DifferentialGradedModule.PropertyI.Resolution B M}
    {J : DifferentialGradedModule.PropertyI.Resolution B N}
    (m : DifferentialGradedModule.PropertyI.Resolution.Map f I J) :
    (InternalHom.derivedSourceFunctor T).map
          ((DifferentialGradedModule.toK B).map m.hom) ≫
        (modelIso T J).hom =
      (modelIso T I).hom ≫
        (InternalHom.derivedFunctor T).map
          ((DifferentialGradedModule.Derived.Q B).map
            ((DifferentialGradedModule.toK B).map f)) := sorry

/-- The inverse resolution-model comparison satisfies the reverse target-naturality square. -/
@[reassoc, stacks 0CS5 "inverse target naturality of the property-I derived internal-Hom model"]
theorem modelIso_inv_naturality_target
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M N : DifferentialGradedModule.{u, v} B} {f : M ⟶ N}
    {I : DifferentialGradedModule.PropertyI.Resolution B M}
    {J : DifferentialGradedModule.PropertyI.Resolution B N}
    (m : DifferentialGradedModule.PropertyI.Resolution.Map f I J) :
    (modelIso T I).inv ≫
        (InternalHom.derivedSourceFunctor T).map
          ((DifferentialGradedModule.toK B).map m.hom) =
      (InternalHom.derivedFunctor T).map
          ((DifferentialGradedModule.Derived.Q B).map
            ((DifferentialGradedModule.toK B).map f)) ≫
        (modelIso T J).inv := sorry

/-- The forward resolution-model comparison is contravariantly natural in the bimodule
source. -/
@[reassoc, stacks 0CS5 "source naturality of the property-I derived internal-Hom model"]
theorem modelIso_hom_naturality_source
    {T T' : DifferentialGradedBimodule.{u, v, w, v} A B} (f : T ⟶ T')
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) :
    (InternalHom.derivedSourceMap f).app
          ((DifferentialGradedModule.toK B).obj I.obj) ≫
        (modelIso T I).hom =
      (modelIso T' I).hom ≫
        (InternalHom.derivedNatTrans f).app
          ((DifferentialGradedModule.Derived.Q B).obj
            ((DifferentialGradedModule.toK B).obj M)) := sorry

/-- The inverse resolution-model comparison satisfies the reverse source-naturality square. -/
@[reassoc, stacks 0CS5 "inverse source naturality of the property-I derived internal-Hom model"]
theorem modelIso_inv_naturality_source
    {T T' : DifferentialGradedBimodule.{u, v, w, v} A B} (f : T ⟶ T')
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) :
    (modelIso T' I).inv ≫
        (InternalHom.derivedSourceMap f).app
          ((DifferentialGradedModule.toK B).obj I.obj) =
      (InternalHom.derivedNatTrans f).app
          ((DifferentialGradedModule.Derived.Q B).obj
            ((DifferentialGradedModule.toK B).obj M)) ≫
        (modelIso T I).inv := sorry

end DifferentialGradedBimodule.InternalHom.Derived.Resolution
