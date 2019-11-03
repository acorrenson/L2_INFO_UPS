------------------------------------
-- Bascule D(elay)
------------------------------------
library ieee;
use ieee.std_logic_1164.all;

entity bascule_d is
  port (
    clk:  inout std_logic;
    d:    in std_logic;
    q:    out std_logic;
    qb:   out std_logic);
end bascule_d;

architecture bascule_d_arch of bascule_d is
begin
  process(clk) begin
    if rising_edge(clk) then
      q <= d;
      qb <= not d;
    end if;
  end process;
end bascule_d_arch;


------------------------------------
-- Test bench
------------------------------------

library ieee;
use ieee.std_logic_1164.all;

entity bascule_d_test is
end bascule_d_test;

architecture bascule_d_test_arch of bascule_d_test is
  signal clk : std_logic;
  signal d : std_logic;
  signal q : std_logic;
  signal qb : std_logic;
begin
  clock: process
    begin
      clk <= '0';
      wait for 20 ns;
      clk <= '1';
      wait for 20 ns;
      clk <= '0';
      wait for 20 ns;
      clk <= '1';
      wait for 20 ns;
      wait;
    end process;
  bascule: entity work.bascule_d port map (clk, d, q, qb);
  process begin
    d <= '1';
    wait for 40 ns;
    d <= '0';
    wait for 40 ns;
    wait;
  end process;
end bascule_d_test_arch;