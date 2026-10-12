/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Naturality
public import ReasLib.CategoryTheory.Fibered.Inertia.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.ToInertia.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Strict
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Pseudofunctor.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.StrongTrans

/-!
# Functoriality of inertia over a base

This aggregate assembles the stable based-inertia API from small layers:

* `Computations.{Maps,Sections}` owns the direct object, automorphism, and arrow readouts for
  the neutral based forgetful maps and identity sections;
* `ToInertia.Computations` owns the corresponding object, automorphism, and arrow readouts for
  the relative-to-absolute comparison;
* `Map` owns relative and absolute inertia maps;
* `Comparison` owns section, identity, and composition comparisons;
* `Naturality` owns the relative-to-absolute comparison;
* `NatTrans.{Construction,Computations,Whiskering}` separates local `2`-cell data,
  component readouts, and whiskering coherence; `Computations.{Action,Naturality,Comparisons}`
  does the same for the ordinary packaged pseudofunctor.
* `Pseudofunctor` and `Strict` own the packaged constructions and direct `map_id`/`map_comp`
  laws, while `Computations.Action.{Objects,TwoCell,LocalAction}` and the strict focused leaves
  expose the ordinary and strict projections separately.
* `StrongTrans.Forget` and `StrongTrans.IdentitySection` separately own the two neutral
  based-inertia transformations; `StrongTrans` is their compatibility aggregate.
* `Relative.Action.{Construction,Computations}` separates the pseudo-comma action data from its
  readouts, while `Relative.Comparison` owns the comparison cells.
* `Relative.Pseudofunctor.{Construction,Computations}` separates coherence assembly from the six
  packaging bridges on arrows over the base.

New developments should import the smallest leaf matching their use. This aggregate remains a
convenience entry point without reintroducing a monolithic owner.
The preferred absolute action surface is
`BasedCategory.Inertia.map`, `BasedCategory.Inertia.map₂`,
`BasedCategory.Inertia.mapFunctor`, and `BasedCategory.Inertia.mapIso`, while
the strict and ordinary packaged views expose `map_id` and `map_comp` directly. The
relative-to-absolute naturality is owned by
`BasedCategory.RelativeInertia.toInertia.naturalityIso`, with objectwise and
underlying-arrow computations in its namespace.
-/
