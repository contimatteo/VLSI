from .storage import CP_data_file_url

###


def convert_txt_file_to_dzn(txt_file_name: str):
    assert isinstance(txt_file_name, str)

    txt_file_url = CP_data_file_url(txt_file_name, "txt")
    dzn_file_url = CP_data_file_url(txt_file_name, "dzn")

    assert txt_file_url.exists() and txt_file_url.is_file()

    #

    with open(txt_file_url, encoding="utf-8") as f:
        txt_lines = f.readlines()
        f.close()

    dzn_lines = ['' for _ in range(len(txt_lines))]
    data_dict = {}

    #

    # print and save width
    width = txt_lines[0][:-1]
    dzn_lines[0] = 'width = ' + width + ';\n'
    data_dict['width'] = int(width)

    # print and save n_plates
    n_plates = txt_lines[1][:-1]
    dzn_lines[1] = 'n_plates = ' + n_plates + ';\n'
    data_dict['n_plates'] = int(n_plates)

    # print and save dims
    data_dict['dims'] = []
    dzn_lines[2] = 'dims = ['
    for line_idx in range(2, len(txt_lines)):
        x, y = txt_lines[line_idx][:-1].split(sep=' ')
        dzn_lines[line_idx] += '|' + x + ', ' + y + ',\n'
        data_dict['dims'].append((int(x), int(y)))

    # remove last comma
    dzn_lines[-1] = dzn_lines[-1][:-1]

    # close the array
    dzn_lines[-1] += '|]'

    #

    with open(dzn_file_url, 'w', encoding="utf-8") as f:
        f.writelines(dzn_lines)
        f.close()

    #

    assert txt_file_url.exists() and txt_file_url.is_file()

    return data_dict
