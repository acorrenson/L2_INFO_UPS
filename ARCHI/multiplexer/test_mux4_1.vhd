----------------------------
-- Test Multiplexeur 2 vers 1
----------------------------


library ieee;
use ieee.std_logic_1164.all;

-- entitee de test pour mux2_1
entity test_mux4_1 is
end test_mux4_1;

-- architecture pour le test
architecture test_mux4_1_arc of test_mux4_1 is
  -- signaux a afficher au debug
  signal input_signals  : std_logic_vector(3 downto 0);
  signal select_signal  : std_logic_vector(1 downto 0);
  signal output_signal  : std_logic;

  -- composant a tester
  component mux4_1
  port (
    input_signals : in std_logic_vector(3 downto 0);
    select_signal : in std_logic_vector(1 downto 0);
    output_signal : out std_logic
  );
  end component;
begin
  -- instance du composant a tester
  mux4_1_inst : mux4_1 port map (
    -- l'interface est la meme que 
    -- celle de l'arhictecture de test !
    -- On connecte donc 1 pour 1.
    input_signals,
    select_signal,
    output_signal
  );

  -- processus de test
  process
    type table_verite is array (0 to 15) of std_logic_vector(3 downto 0);
    type table_selection is array (0 to 3) of std_logic_vector(1 downto 0);
    -- entrees possibles
    constant tdv : table_verite := 
      ( "0000", "0001", "0010", "0011",
        "0100", "0101", "0110", "0111",
        "1000", "1001", "1010", "1011",
        "1100", "1101", "1110", "1111");
    -- selections possibles
    constant tds : table_selection :=
      ("00", "01", "10", "11");
  begin
    -- test de toutes les combinaisons
    for i in tds'range loop
      for j in tdv'range loop
        select_signal <= tds(i);
        input_signals <= tdv(j);
        wait for 5 ns;
      end loop;
    end loop;
    
    wait;
  end process;

end test_mux4_1_arc;