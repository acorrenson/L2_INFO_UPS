----------------------------
-- Test Multiplexeur 2 vers 1
----------------------------


library ieee;
use ieee.std_logic_1164.all;

-- entitee de test pour mux2_1
entity test_mux2_1 is
end test_mux2_1;

-- architecture pour le test
architecture test_mux2_1_arc of test_mux2_1 is
  -- signaux a afficher au debug
  signal input_signals : std_logic_vector(1 downto 0);
  signal select_signal : std_logic;
  signal output_signal : std_logic;

  -- composant a tester
  component mux2_1
  port (
    input_signals : in std_logic_vector(1 downto 0);
    select_signal : in std_logic;
    output_signal : out std_logic
  );
  end component;
begin
  -- instance du composant a tester
  mux2_1_inst : mux2_1 port map (
    -- l'interface est la meme que 
    -- celle de l'arhictecture de test !
    -- On connecte donc 1 pour 1.
    input_signals,
    select_signal,
    output_signal
  );

  -- processus de test
  process
    type table_verite is array (0 to 3) of std_logic_vector(1 downto 0);
    constant tdv : table_verite := ("00", "01", "10", "11");
  begin
    -- table pour selection
    -- du signal 0
    select_signal <= '0';
    for i in tdv'range loop
      input_signals <= tdv(i);
      wait for 5 ns;
    end loop;

    -- table pour selection
    -- du signal 1
    select_signal <= '1';
    for i in tdv'range loop
      input_signals <= tdv(i);
      wait for 5 ns;
    end loop;
    
    wait;
  end process;

end test_mux2_1_arc;