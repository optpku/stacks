/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Comma.Basic
public import ReasLib.CategoryTheory.Bicategory.Comma.Map
public import ReasLib.CategoryTheory.Bicategory.Comma.Projection
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.Iso
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.Map
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.MapArrow
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.ChangeLegs
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Basic

/-!
# Bicategorical comma constructions

This is the compatibility entry point for the bicategorical comma hierarchy.
The reusable declarations are owned by focused leaves:

- `Comma.Basic` owns the two-sided colax comma data and bicategory structure;
- `Comma.Map` owns postcomposition by a pseudofunctor;
- `Comma.Projection` owns endpoint projections, comparison, and universal lifts;
- `Comma.Pseudo` owns the invertible-comparison specialization;
- `Comma.Pseudo.Iso` owns endpointwise construction of pseudo comma isomorphisms;
- `Comma.Pseudo.MapArrow` owns the action of a pseudofunctor on bicategorical arrows;
- `Comma.Pseudo.ChangeLegs` owns change of the two pseudo comma legs;
- `CostructuredArrow.Basic` owns terminal-right-leg specializations and slices.

Existing users may continue to import this module. New developments can import the
smallest leaf that provides the required construction. `Pseudo.Map` supplies
functoriality under a common target pseudofunctor, `Pseudo.MapArrow` supplies
the componentwise arrow action, and `Pseudo.ChangeLegs` supplies
contravariant-left and covariant-right functoriality in the two legs.
-/
