module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.FullyFaithful
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Functor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Hom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Hom.Model
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Hom.Cohomology
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Regular
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.SelfExt

/-!
# Derived tensoring with a complex on a ringed site

Compatibility entry point for the derived tensor API.  The implementation is split by
mathematical role:

* `Derived.Functor` owns the total left-derived tensor functor;
* `Derived.Hom` owns its abstract source and target derived Hom bifunctors;
* `Derived.Adjunction` owns its derived enriched representable right adjoint;
* `Derived.Regular` owns the image of the regular DG module;
* `Derived.SelfExt` owns the comparison on shifted self-Homs;
* `Derived.FullyFaithful` owns the compact-generator full-faithfulness result.

Downstream developments should import the narrow leaf they use.  This module re-exports the
former monolithic surface so existing imports remain valid.
-/

@[expose] public section
