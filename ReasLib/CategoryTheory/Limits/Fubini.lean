/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Fubini.DiagramOfCocones.Totalization
public import ReasLib.CategoryTheory.Limits.Fubini.DiagramOfCocones.Equivalence
public import ReasLib.CategoryTheory.Limits.Fubini.DiagramOfCones.Totalization
public import ReasLib.CategoryTheory.Limits.Fubini.DiagramOfCones.Equivalence
public import ReasLib.CategoryTheory.Limits.Fubini.Colimits
public import ReasLib.CategoryTheory.Limits.Fubini.Limits

/-!
# Fubini totalization for cone and cocone categories

Compatibility aggregate for the Fubini totalization API. Focused consumers
should import the smallest applicable leaf:

* `DiagramOfCocones.Totalization` for cocone totalization and its row-point functor;
* `DiagramOfCocones.Equivalence` for the cocone-category equivalence;
* `DiagramOfCones.Totalization` for the dual cone construction;
* `DiagramOfCones.Equivalence` for the cone-category equivalence;
* `Colimits.Basic` for colimit transport and existence;
* `Colimits.Comparison` for canonical iterated/total colimit isomorphisms;
* `Colimits.Computations` for their component formulas;
* `Limits.Basic` for the dual limit transport and existence API;
* `Limits.Comparison` for canonical iterated/total limit isomorphisms; or
* `Limits.Computations` for their component formulas.

The historical `Colimits` and `Limits` imports are compatibility aggregates over their three
focused leaves.

Rowwise universal cones and cocones identify the corresponding outer (co)cone category with the
(co)cone category of the uncurried diagram. This supplies functorial totalization, preservation
and reflection of universal properties, and canonical comparison isomorphisms for the two orders
of iteration.

The abstraction here follows the universal-property viewpoint: a colimit is a universal cocone,
equivalently an initial object of its cocone category, and an iterated colimit is the composition
of left Kan extensions to terminal categories. Consequently totalization is defined first as a
functor on entire cocone categories, without universal hypotheses. Pointwise colimit cocones then
make this functor an equivalence, from which preservation, reflection, existence, and comparison
isomorphisms are separate fine-grained consequences. The cone construction is kept exactly dual.
The final curry bridge only transports along `currying.symm.unitIso`; it does not contaminate the
reusable `uncurry.obj F` infrastructure with product-specific bookkeeping.

Proof-refinement roadmap for the statement placeholders in these leaves:

* total cocone/cone naturality: decompose a product morphism and combine row naturality,
  `D.map` compatibility, and outer (co)cone naturality;
* functor laws: use `CoconeMorphism.ext` or `ConeMorphism.ext` on the unchanged vertex map;
* unit/counit component formulas: use `IsColimit.fac`/`hom_ext` or their limit duals;
* naturality and triangle identities: extensionality reduces them to identities on vertex maps.

The total (co)cones and the universal-property transports have explicit non-`Prop` data;
refinement only discharges their law fields.
-/
