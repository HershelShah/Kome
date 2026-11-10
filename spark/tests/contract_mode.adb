with Ada.Text_IO;

package body Contract_Mode with SPARK_Mode => Off is

   function Contracts_On return Boolean is
      On : Boolean := False;
      --  Called only if the pragma Assert below executes.
      function Mark return Boolean is
      begin
         On := True;
         return True;
      end Mark;
   begin
      pragma Assert (Mark);
      return On;
   end Contracts_On;

   procedure Skip (What : String) is
   begin
      Ada.Text_IO.Put_Line ("SKIP " & What & " (release mode: contracts are not evaluated)");
   end Skip;

end Contract_Mode;
