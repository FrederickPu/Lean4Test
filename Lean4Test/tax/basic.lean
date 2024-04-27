import Mathlib.Data.Real.Basic

/- when formalizing tax code we have three major obstacles:
  1. Every law introduces new terminology (attributes) that a person may have, as such it becomes infeasible to have all the attribute of a person contained in a single structure or class.
  2. We need a way to treat forms such as T4 forms as first class objects in that they are the primary source of truth for all information about a person
  3. Legal terminology mostly uses default logic, that is the default case is listed first and then exemptions and exceptions are listed afterwards.
-/

/-
  1. can be solved using type classes
  Attributes can thought of as typeclasses (abstract data types that can be implemented by concrete types).
  Consider the following example:
-/

class Age (T : Type*) where
  age_in_years : T → ℝ

/- A type `T` (which can be thought of as a collection of things) implements the Age class
  if there is a function Age.age that can provide the age of any member `t` of that type `T`
  Note: for the same type `T` you can have multiple instances of `Age T`, for example if `T` is the type of people, we can consider a person who has just been born to be 0 years old (counting since birth) or 1 years old (counting since conception).
  Age is an abtract attribute that can be implemented by multiple types (for example both cars and people have Age).
  And inorder for a type `Car` implement an this Age attribute, we need to provide a function age_in_years that takes in a `Car` and returns a real number.

  To see this in action, consider the following concrete type:
-/

structure SimplePerson where
  birthday_in_years_AfterChrist : ℝ
  name : String

/-
  We can show that SimplePerson implments Age as follows:
  Where the age_in_years is calculated assuming the date is 2022
-/

instance : Age (SimplePerson) where
  age_in_years := fun person => 2022 - person.birthday_in_years_AfterChrist

/-
  Note that lean typeclasses can have as many required properties as you like for example:
-/

class AgeComplicated (T : Type*) where
  age_in_years : T → ℝ
  age_in_dog_years : T → ℝ
  favouriteColor : T → String

/- In this case we could implment this typeclass as follows -/

instance : AgeComplicated (SimplePerson) where
  age_in_years := fun person => 2022 - person.birthday_in_years_AfterChrist
  age_in_dog_years := fun person => (2022 - person.birthday_in_years_AfterChrist) * 7
  favouriteColor := fun person => if person.name = "Bob" then "purple" else "blue"

/- Now a laws can defined on any type that implement all of the abstract attributes that the law describes -/

class Income (T : Type*) where
  income_in_cad : T → ℝ

/- The below taxcode states that the income tax for an individual is 0 if there are under 18 and 12% of their income otherwise-/
def income_tax {T : Type*} [Age T] [Income T] (t : T) : ℝ :=
  if Age.age_in_years t < 18 then 0 else Income.income_in_cad t * 0.12

/- Note that in this a model if an ostrich had income, then we would be able to compute it's income tax -/

/- 2. we can now consider a person as a list of tax-forms (T4, T5 etc) that which can then later be used to implement the abstract attributes defined in the taxcode laws.-/

/-
 3. can be solved using syntax sugars.
 We saw that `if then else` can be used as a sugar for `ite`
 We can also make a sugar (called macros in lean) that maps `C unless A then B` to `if A then B else C`
-/

/-
  4. Similarly we never want to define a tax function explicitly.
  ie: def cumulative_tax : t → ℝ := fun x => income_tax x + property_tax x
  This is because it is cumbersome to have to write each type of tax twices. If we were to construct a new tax (say carbon tax)
  we would need to manually update the cumulative tax function.

  This creates major safety concerns since the cumulative tax function could easily omit new taxcodes by accident.
-/

/-
  To resolve this issue we can use decoractors:

  ```
  @[tax_code]
  def income_tax {T : Type*} [Age T] [Income T] (t : T) : ℝ :=
  if Age.age_in_years t < 18 then 0 else Income.income_in_cad t * 0.12

  @[tax_code]
  def property_tax {T : Type*} [Property T] (t : T) : ℝ := sorry
  ```

  From which we can automatically extract a cumulative tax function using a custom defined tactic:
  ```
  def cumulative_tax {T : Type*} [Age T] [Income T] [Property T] (x : T) : ℝ := by
    tax_code x
  ```

  Which is equivalent to adding all of the taxe_code that apply to that individual
  ```
  def cumulative_tax {T : Type*} [Age T] [Income T] [Property T] : ℝ := by
    exact income_tax t + property_tax t
  ```
  If the user wants to see the reduced form they can use `tax_code? x` which will allow them to replace it with the explicit expression in a similar way to exact?

  Note that if there were instead tax_code for which `x` cannot be taxed such as:
  ```
     @[tax_code]
  def carbon_tax {T : Type*} [CarbonFootPrint T] (t : T) : ℝ := sorry
  ```
  Then, tax_code would throw an error, indicating that the cumulative tax is not well defined and that the underlying type `T` requires needs to implement more tax-codes in order to conform to the new tax-code.
  ```
  def cumulative_tax {T : Type*} [Age T] [Income T] [Property T] : ℝ := by
    /-
      cumulative tax cannot be defined because `x`'s type `T` is missing attributes from the following tax_code:

        @[tax_code]
        def property_tax {T : Type*} [Property T] (t : T) : ℝ

      attributes: [Property T] are missing
    -/
    tax_code x
  ```
-/
