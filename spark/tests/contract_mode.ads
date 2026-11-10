--  Contract_Mode: the build mode of a test main, read at run time
--  (kome_spark.gpr, SIMPLIFY.md S24). In the check mode (-gnata) every
--  contract executes; in the release mode (-XMode=release, release.adc)
--  none does. A check that a precondition refuses a call has nothing to
--  observe in release mode, and the call would run the body on an input
--  that its Pre excludes. Thus such a check runs only when Contracts_On,
--  and the main prints a SKIP line for it otherwise. This file is a
--  helper of the test mains, not a module (it is not tests/test_*.adb).
package Contract_Mode with SPARK_Mode => Off is

   --  True iff assertions execute in this build (check mode).
   function Contracts_On return Boolean;

   --  Print "SKIP <What> (release mode: contracts are not evaluated)".
   procedure Skip (What : String);

end Contract_Mode;
