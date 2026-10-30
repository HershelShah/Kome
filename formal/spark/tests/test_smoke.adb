pragma Ada_2022;
with Ada.Text_IO; use Ada.Text_IO;
with Kome; use Kome;
procedure Test_Smoke with SPARK_Mode => Off is
   A : constant Byte_Array (0 .. 3) := [1, 2, 3, 4];
begin
   Put_Line ((if A'Length = 4 and Error'Pos (Err_Corrupt) = 7 then "PASS smoke" else "FAIL smoke"));
end Test_Smoke;
