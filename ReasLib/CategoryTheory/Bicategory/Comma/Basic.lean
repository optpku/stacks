/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Comma.Basic.Data
public import ReasLib.CategoryTheory.Bicategory.Comma.Basic.Bicategory
public import ReasLib.CategoryTheory.Bicategory.Comma.Basic.Computation

/-!
# Colax comma bicategories

Compatibility entry point for the two-sided colax comma hierarchy:

- `Comma.Basic.Data` owns objects, `1`-morphisms, and `2`-morphisms;
- `Comma.Basic.Bicategory` owns the bicategory assembly and comma cell constructors;
- `Comma.Basic.Computation` owns componentwise rewriting and local-groupoid API.

Existing users may continue to import this module. New developments can import
the smallest leaf that provides the required construction.
-/
